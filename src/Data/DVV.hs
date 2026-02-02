{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- |
Module      : Data.DVV
Description : Dotted Version Vectors for causal tracking and conflict detection
Copyright   : (c) James R. Thompson
License     : BSD3
Stability   : experimental

Dotted Version Vectors (DVVs) provide a mechanism for tracking causality
and detecting conflicts in distributed systems. This implementation supports
efficient synchronization, event recording, and conflict resolution.
-}
module Data.DVV (
  -- * Core Types
  Count,
  Dot (..),
  VersionVector,
  mkVersionVector,
  getVersionVectorCounts,
  DVV (..),

  -- * Operations
  sync,
  context,
  event,
  values,
  prune,
  reconcile,
  lww,

  -- * Analysis
  size,
  extractComponents,
)
where

import Algebra.PartialOrd (PartialOrd (..))
import Data.Function (on)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as Map
import Data.Hashable (Hashable (..))
import Data.List (foldl', foldl1', sort, sortBy)
import Data.Maybe (fromMaybe)
import Data.Word (Word64)
import GHC.Generics (Generic)

-- | A logical actor's count, 1-indexed, positive only.
type Count = Word64

-- | A Dot is a pair of a replica ID and a logical counter.
data Dot actorID = Dot !actorID !Count
  deriving stock (Eq, Show, Functor, Generic)

{- | Dots are partially ordered: two dots are comparable if and only if they
share the same actor ID, in which case they are ordered by their counter.
-}
instance (Eq actorID) => PartialOrd (Dot actorID) where
  leq (Dot a1 c1) (Dot a2 c2) = a1 == a2 && c1 <= c2
  comparable (Dot a1 _) (Dot a2 _) = a1 == a2

{- | Dot is a pair of an actor (identifier) and a logical counter,
but we hash using the actor value only.
-}
instance (Hashable actorID) => Hashable (Dot actorID) where
  hashWithSalt salt (Dot actorID _) = hashWithSalt salt actorID

{- | A Version Vector is a mapping from actor IDs to their latest known counter.
It stores a list of counts to actors for efficient leq checks.
Requires keys to be Hashable.
-}
data VersionVector actorID = VersionVector
  { vvMap :: HashMap actorID Count
  , vvDesc :: [(Count, actorID)]
  }
  deriving stock (Show, Generic)

instance (Eq actorID) => Eq (VersionVector actorID) where
  (VersionVector m1 _) == (VersionVector m2 _) = m1 == m2

instance (Hashable actorID, Eq actorID) => PartialOrd (VersionVector actorID) where
  leq (VersionVector _ sortedList) (VersionVector m2 _) =
    all (\(c, a) -> c <= Map.findWithDefault 0 a m2) sortedList

-- | Helper to construct valid VersionVector
mkVersionVector :: HashMap actorID Count -> VersionVector actorID
mkVersionVector m =
  VersionVector
    m
    ( sortDesc fst $
        map (\(a, c) -> (c, a)) (Map.toList m)
    )
 where
  sortDesc keyFn = sortBy (\x y -> compare (keyFn y) (keyFn x))

-- | Helper to extract the map of counts from a VersionVector, we hide the other field accessors
getVersionVectorCounts :: VersionVector actorID -> HashMap actorID Count
getVersionVectorCounts (VersionVector m _) = m

{- | A Dotted Version Vector (DVV) consisting of a Causal History (Version Vector)
and a set of concurrent values associated with Dots.

Note: A Singleton has no causal history, its counter is implicitly 1.

@actorID@ is the type of actor IDs. Must be Hashable.
@value@ is the type of the value stored.
-}
data DVV actorID value
  = EmptyDVV
  | SingletonDVV !actorID !value
  | DVV !(VersionVector actorID) !(HashMap (Dot actorID) value)
  deriving stock (Generic)

instance (Hashable actorID, Eq value) => Eq (DVV actorID value) where
  EmptyDVV == EmptyDVV = True
  SingletonDVV a1 v1 == SingletonDVV a2 v2 = a1 == a2 && v1 == v2
  DVV vv1 dots1 == DVV vv2 dots2 = vv1 == vv2 && dots1 == dots2
  l == SingletonDVV a2 v2 = l == event EmptyDVV Nothing a2 v2
  SingletonDVV a1 v1 == r = event EmptyDVV Nothing a1 v1 == r
  _ == _ = False

instance
  (Show actorID, Show value, Ord actorID, Hashable actorID) =>
  Show (DVV actorID value)
  where
  show dvv =
    case dvv of
      EmptyDVV -> "([],[])"
      _ ->
        let (_, dots) = extractComponents dvv
            ctx = getVersionVectorCounts (context dvv)
            allActors = sort (Map.keys ctx)
            dotsList = Map.toList dots
            groupedValues a =
              map snd $
                sortBy (flip compare `on` (\(Dot _ c, _) -> c)) $
                  filter (\(Dot a' _, _) -> a' == a) dotsList

            formattedEntries = [(a, Map.findWithDefault 0 a ctx, groupedValues a) | a <- allActors]
         in show (formattedEntries, [] :: [value])

isSeenBy ::
  (Ord actorID, Hashable actorID) =>
  Dot actorID ->
  DVV actorID value ->
  Bool
isSeenBy (Dot i n) dvv =
  case dvv of
    EmptyDVV -> False
    SingletonDVV a _ ->
      -- A dot is seen by a singleton if it's the same dot (or 0)
      Dot i n == Dot a 1
    DVV vv dots ->
      -- 1. Check if the counter is within the compacted summary
      n <= Map.findWithDefault 0 i (vvMap vv)
        ||
        -- 2. OR check if this specific dot is in the active set
        Map.member (Dot i n) dots

-- | DVV partial order is defined by the partial order of their causal histories.
instance (Hashable actorID, Eq value, Ord actorID) => PartialOrd (DVV actorID value) where
  leq EmptyDVV _ = True
  leq _ EmptyDVV = False
  leq (SingletonDVV i1 _) d2 = Dot i1 1 `isSeenBy` d2 -- counters start at 1
  leq (DVV vv1 dots1) d2 =
    let vv2 = case d2 of
          DVV v _ -> v
          _ -> mkVersionVector Map.empty -- EmptyDVV and SingletonDVV have no causal history
     in leq vv1 vv2 && all (`isSeenBy` d2) (Map.keys dots1)

instance (Hashable actorID, Ord value, Ord actorID) => Ord (DVV actorID value) where
  compare a b
    | a == b = EQ
    | leq a b = LT
    | leq b a = GT
    | otherwise =
        let (vv1, _) = extractComponents a
            (vv2, _) = extractComponents b
         in if not (leq vv1 vv2)
              then LT
              else GT

-- | Extract all values currently in the DVV.
values :: DVV actorID value -> [value]
values EmptyDVV = []
values (SingletonDVV _ v) = [v]
values (DVV _ vals) = Map.elems vals

-- | Returns the causal context (Version Vector) of the DVV.
context ::
  (Hashable actorID) =>
  DVV actorID value ->
  VersionVector actorID
context EmptyDVV = mkVersionVector Map.empty
context (SingletonDVV actor _) = mkVersionVector (Map.singleton actor 1)
context (DVV causalHistory vals) =
  let finalMap = foldl' updateVec (vvMap causalHistory) (Map.keys vals)
   in mkVersionVector finalMap
 where
  updateVec m (Dot actor counter) = Map.insertWith max actor counter m

-- | Safely extracts the components of any DVV state into a standard history map and values map.
extractComponents ::
  (Hashable actorID) =>
  DVV actorID value ->
  (VersionVector actorID, HashMap (Dot actorID) value)
extractComponents EmptyDVV = (mkVersionVector Map.empty, Map.empty)
extractComponents (SingletonDVV actor val) = (mkVersionVector Map.empty, Map.singleton (Dot actor 1) val)
extractComponents (DVV vec vals) = (vec, vals)

-- | Synchronize (merge) two DVVs.
sync ::
  (Hashable actorID, Ord value) =>
  DVV actorID value ->
  DVV actorID value ->
  DVV actorID value
sync EmptyDVV d = d
sync d EmptyDVV = d
sync d1 d2 =
  let (vL, valsL) = extractComponents d1
      (vR, valsR) = extractComponents d2
   in merge vL valsL vR valsR

-- | Internal merge logic for general DVV components.
merge ::
  (Hashable actorID, Ord value) =>
  VersionVector actorID ->
  HashMap (Dot actorID) value ->
  VersionVector actorID ->
  HashMap (Dot actorID) value ->
  DVV actorID value
merge vL valsL vR valsR =
  let newVec = Map.unionWith max (vvMap vL) (vvMap vR)
      -- Use unionWith to handle duplicate dots consistently (pick min for determinism)
      candidates = Map.unionWith min valsL valsR
      isActive (Dot actor counter) _ =
        case Map.lookup actor newVec of
          Nothing -> True
          Just maxC -> counter > maxC
      newVals = Map.filterWithKey isActive candidates
   in case Map.toList newVals of
        [] -> EmptyDVV
        [(Dot actor 1, val)] | Map.null newVec -> SingletonDVV actor val
        _ -> DVV (mkVersionVector newVec) newVals

-- | Record a new event (update).
event ::
  (Hashable actorID) =>
  -- | The current local DVV state
  DVV actorID value ->
  -- | The Context provided by the client (optional)
  Maybe (VersionVector actorID) ->
  -- | The Actor generating this event
  actorID ->
  -- | The new value
  value ->
  DVV actorID value
event currentState maybeContext actorID newValue =
  let ctx = fromMaybe (mkVersionVector Map.empty) maybeContext
      (causalHistory, vals) = extractComponents currentState
      currentMax = Map.lookup actorID (vvMap (context currentState))
      nextCount = maybe 1 (+ 1) currentMax
      newDot = Dot actorID nextCount

      filterOld (Dot i c) _ =
        case Map.lookup i (vvMap ctx) of
          Nothing -> True
          Just cnt -> c > cnt

      filteredVals = Map.filterWithKey filterOld vals
      newVec = Map.unionWith max (vvMap causalHistory) (vvMap ctx)
      finalVals = Map.insert newDot newValue filteredVals
   in DVV (mkVersionVector newVec) finalVals

-- | Prune the causal history (Version Vector).
prune ::
  -- | Threshold count for pruning
  Count ->
  -- | DVV to prune
  DVV actorID value ->
  DVV actorID value
prune _ EmptyDVV = EmptyDVV
prune _ s@(SingletonDVV _ _) = s
prune threshold (DVV causalHistory vals) =
  let newVec = Map.filter (>= threshold) (vvMap causalHistory)
   in DVV (mkVersionVector newVec) vals

-- | Reconcile multiple siblings into a single value using a merge strategy.
reconcile ::
  (Hashable actorID) =>
  -- | Merge function, take two values and deduce a new value (n.b. it's fine to just pick one of the inputs)
  (value -> value -> value) ->
  -- | The actor ID that will "own" the new reconciled event.
  actorID ->
  -- | The DVV to reconcile.
  DVV actorID value ->
  DVV actorID value
reconcile _ _ EmptyDVV = EmptyDVV
reconcile _ _ s@(SingletonDVV _ _) = s
reconcile mergeFn actorID dvv
  | size dvv <= 1 = dvv
  | otherwise =
      let allVals = values dvv
          -- Foldl1' is safe because of guard size > 1 implies >= 2 elements (at least 2, actually size 0/1 handled)
          -- But size counts elements. Empty=0, Singleton=1, DVV may have 0 in map?
          -- DVV constructor usually ensures non-empty map if used correctly, or use EmptyDVV.
          -- But let's follow existing logic.
          mergedVal = foldl1' mergeFn allVals
          ctx = context dvv
       in event dvv (Just ctx) actorID mergedVal

{- | Last-Write-Wins (LWW) reconciliation.

Reduces multiple concurrent values (siblings) into a single "winning" value based on the provided
comparison function. This operation creates a new event (dot) for the winning value that
supersedes all current values in the DVV.

If there are zero or one values, the DVV is returned unchanged.
-}
lww ::
  (Hashable actorID) =>
  -- | A function to compare two values. 'GT' indicates the first value wins.
  (value -> value -> Ordering) ->
  -- | The actor ID that will "own" the new reconciled event.
  actorID ->
  -- | The DVV to reconcile.
  DVV actorID value ->
  DVV actorID value
lww compareFn = reconcile pickBest
 where
  pickBest v1 v2 = case compareFn v1 v2 of
    GT -> v1
    _ -> v2

-- | Return the number of elements (siblings) in the DVV.
size :: DVV actorID value -> Int
size EmptyDVV = 0
size (SingletonDVV _ _) = 1
size (DVV _ vals) = Map.size vals
