{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      : Data.DVV
-- Description : Dotted Version Vectors for causal tracking and conflict detection
-- Copyright   : (c) James R. Thompson
-- License     : BSD3
-- Stability   : experimental
--
-- Dotted Version Vectors (DVVs) provide a mechanism for tracking causality
-- and detecting conflicts in distributed systems. This implementation supports
-- efficient synchronization, event recording, and conflict resolution.
module Data.DVV
  ( -- * Core Types
    Count,
    Dot (..),
    VersionVector,
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
  )
where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as Map
import Data.Hashable (Hashable (hashWithSalt))
import Data.List (foldl', foldl1')
import Data.Maybe (fromMaybe)
import Data.Word (Word64)
import GHC.Generics (Generic)

-- | A logical actor's count, 1-indexed, positive only.
type Count = Word64

-- | A Dot is a pair of a replica ID and a logical counter.
data Dot actorID = Dot !actorID !Count
  deriving stock (Eq, Show, Ord, Functor, Foldable, Traversable, Generic)

-- | Dot is a pair of an actor (identifier) and a logical counter,
-- but we hash using the actor value only.
instance (Hashable actorID) => Hashable (Dot actorID) where
  hashWithSalt salt (Dot actorID _) = hashWithSalt salt actorID

-- | A Version Vector is a mapping from actor IDs to their latest known counter.
-- Requires keys to be Hashable.
type VersionVector actorID = HashMap actorID Count

-- | A Dotted Version Vector (DVV) consisting of a Causal History (Version Vector)
-- and a set of concurrent values associated with Dots.
--
-- Note: A Singleton has no causal history, its counter is implicitly 1.
--
-- @actorID@ is the type of actor IDs. Must be Hashable.
-- @value@ is the type of the value stored.
data DVV actorID value
  = EmptyDVV
  | SingletonDVV !actorID !value
  | DVV !(VersionVector actorID) !(HashMap (Dot actorID) value)
  deriving stock (Eq, Show, Ord, Functor, Foldable, Traversable, Generic)

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
context EmptyDVV = Map.empty
context (SingletonDVV actor _) = Map.singleton actor 1
context (DVV causalHistory vals) =
  foldl' updateVec causalHistory (Map.keys vals)
  where
    updateVec m (Dot actor counter) = Map.insertWith max actor counter m

-- | Safely extracts the components of any DVV state into a standard history map and values map.
extractComponents ::
  (Hashable actorID) =>
  DVV actorID value ->
  (VersionVector actorID, HashMap (Dot actorID) value)
extractComponents EmptyDVV = (Map.empty, Map.empty)
extractComponents (SingletonDVV actor val) = (Map.empty, Map.singleton (Dot actor 1) val)
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
  let newVec = Map.unionWith max vL vR
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
        _ -> DVV newVec newVals

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
  let ctx = fromMaybe Map.empty maybeContext
      (causalHistory, vals) = extractComponents currentState
      currentMax = Map.lookup actorID (context currentState)
      nextCount = maybe 1 (+ 1) currentMax
      newDot = Dot actorID nextCount

      filterOld (Dot i c) _ =
        case Map.lookup i ctx of
          Nothing -> True
          Just cnt -> c > cnt

      filteredVals = Map.filterWithKey filterOld vals
      newVec = Map.unionWith max causalHistory ctx
      finalVals = Map.insert newDot newValue filteredVals
   in DVV newVec finalVals

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
  let newVec = Map.filter (>= threshold) causalHistory
   in DVV newVec vals

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
          mergedVal = foldl1' mergeFn allVals
          ctx = context dvv
       in event dvv (Just ctx) actorID mergedVal

-- | Last-Write-Wins (LWW) reconciliation.
--
-- Reduces multiple concurrent values (siblings) into a single "winning" value based on the provided
-- comparison function. This operation creates a new event (dot) for the winning value that
-- supersedes all current values in the DVV.
--
-- If there are zero or one values, the DVV is returned unchanged.
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
