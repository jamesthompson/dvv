{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-orphans #-}

import Algebra.PartialOrd (PartialOrd (..))
import Control.Monad (foldM)
import Data.DVV
import qualified Data.HashMap.Strict as Map
import Data.Hashable (Hashable)
import Test.Hspec hiding (context)
import Test.QuickCheck

-- Helper to make tests more readable
type ID = String

type Value = String

main :: IO ()
main = hspec $ do
  describe "DVV Operations" $ do
    it "should yield the correct size, values, and context for an empty DVV" $ do
      let d = EmptyDVV :: DVV ID Value
      size d `shouldBe` 0
      values d `shouldBe` []
      context d `shouldBe` mkVersionVector Map.empty

    it "should yield the correct size, values, and context for a singleton DVV" $ do
      let d = SingletonDVV "A" "v1" :: DVV ID Value
      size d `shouldBe` 1
      values d `shouldBe` ["v1"]
      context d `shouldBe` mkVersionVector (Map.fromList [("A", 1)])

    it "should handle events correctly (update)" $ do
      -- A starts with v1
      let d0 = SingletonDVV "A" "v1" :: DVV ID Value

      -- A updates with v2, knowing about d0
      let ctx0 = context d0
      let d1 = event d0 (Just ctx0) "A" "v2"

      size d1 `shouldBe` 1
      values d1 `shouldBe` ["v2"]
      context d1 `shouldBe` mkVersionVector (Map.fromList [("A", 2)])

      -- A updates again with v3
      let ctx1 = context d1
      let d2 = event d1 (Just ctx1) "A" "v3"

      size d2 `shouldBe` 1
      values d2 `shouldBe` ["v3"]
      context d2 `shouldBe` mkVersionVector (Map.fromList [("A", 3)])

    it "should handle concurrent updates (siblings)" $ do
      -- A starts with v1
      let d0 = SingletonDVV "A" "v1" :: DVV ID Value

      -- B also starts with v2 (concurrent to A:v1)
      let dOther = SingletonDVV "B" "v2" :: DVV ID Value

      -- Sync them
      let dSync = sync d0 dOther
      size dSync `shouldBe` 2
      values dSync `shouldContain` ["v1"]
      values dSync `shouldContain` ["v2"]
      context dSync `shouldBe` mkVersionVector (Map.fromList [("A", 1), ("B", 1)])

    it "should resolve siblings with event superseding" $ do
      -- Start with synced state having {A:1, v1} and {B:1, v2}
      let d0 = SingletonDVV "A" "v1" :: DVV ID Value
          dOther = SingletonDVV "B" "v2"
          dSync = sync d0 dOther

      -- A updates. A knows about the whole context of dSync.
      let ctx = context dSync
          dFinal = event dSync (Just ctx) "A" "v3"

      size dFinal `shouldBe` 1
      values dFinal `shouldBe` ["v3"]
      -- Dot should be A:2. Context should be {A: 2, B: 1}
      context dFinal `shouldBe` mkVersionVector (Map.fromList [("A", 2), ("B", 1)])

    it "should keep concurrent updates if context is missing information" $ do
      -- B makes an update v1
      let dB = SingletonDVV "B" "v1" :: DVV ID Value

      -- A makes an update v2, but A DOES NOT KNOW about B.
      let dA = SingletonDVV "A" "v2"

      -- Sync them. Should have both.
      let dSync = sync dA dB

      -- A updates again, using only A's context.
      let ctxA = context dA
          dFinal = event dSync (Just ctxA) "A" "v3"

      -- v2 (A:1) is superseded. v1 (B:1) is NOT.
      size dFinal `shouldBe` 2
      values dFinal `shouldContain` ["v1"]
      values dFinal `shouldContain` ["v3"]
      context dFinal `shouldBe` mkVersionVector (Map.fromList [("A", 2), ("B", 1)])

    it "should handle multiple siblings from different actors" $ do
      let dA = SingletonDVV "A" "v1" :: DVV ID Value
          dB = SingletonDVV "B" "v2"
          dC = SingletonDVV "C" "v3"

          dAB = sync dA dB
          dABC = sync dAB dC

      size dABC `shouldBe` 3
      context dABC
        `shouldBe` mkVersionVector (Map.fromList [("A", 1), ("B", 1), ("C", 1)])

    it "should prune old history" $ do
      -- Create a DVV with history {A: 10, B: 5}
      let d0 = SingletonDVV "A" "v1" :: DVV ID Value
          d10 = foldl (\d i -> event d (Just $ context d) "A" (show @Int i)) d0 [2 .. 10]
          dB = SingletonDVV "B" "vB"
          dB5 = foldl (\d i -> event d (Just $ context d) "B" (show @Int i)) dB [2 .. 5]

          dSync = sync d10 dB5

      context dSync `shouldBe` mkVersionVector (Map.fromList [("A", 10), ("B", 5)])

      -- To test prune properly, we need history that IS NOT supported by a value.
      -- Make A supersede B:5 first (so B:5 is removed from values), but B:5 remains in history.
      let dVoidB = event dSync (Just $ context dSync) "A" "superseding-everything"

      -- Now A:11. B:5 is superseded (removed from values).
      -- Values: {A:11}. Vector: {A:11, B:5} (merged context).
      context dVoidB `shouldBe` mkVersionVector (Map.fromList [("A", 11), ("B", 5)])

      let dPruned = prune 8 dVoidB
      -- Now B:5 < 8, so it should be removed from vector.
      -- A:11 >= 8, keeps A:11.
      context dPruned `shouldBe` mkVersionVector (Map.fromList [("A", 11)])

    it "should reconcile siblings into a single value with new dot" $ do
      let dA = SingletonDVV "A" "v1" :: DVV ID Value
          dB = SingletonDVV "B" "v2"
          dSync = sync dA dB

      size dSync `shouldBe` 2

      -- Reconcile with "concatenation"
      let dReconciled = reconcile (\a b -> a ++ b) "C" dSync

      size dReconciled `shouldBe` 1
      let val = head (values dReconciled)
      val `shouldSatisfy` (\v -> v == "v1v2" || v == "v2v1")

      -- Context should now include C:1
      context dReconciled
        `shouldBe` mkVersionVector (Map.fromList [("A", 1), ("B", 1), ("C", 1)])

    it "should use Last-Write-Wins (lww) to pick a winner" $ do
      let dA = SingletonDVV "A" "apple" :: DVV ID Value
          dB = SingletonDVV "B" "banana"
          dSync = sync dA dB

      -- lww with string comparison (lexicographical)
      let dLWW = lww compare "A" dSync

      size dLWW `shouldBe` 1
      values dLWW `shouldBe` ["banana"] -- banana > apple

      -- Reconcile advances the dot for the actor performing the reconcile (A).
      -- Previous A was 1. New dot is A:2.
      -- B remains at 1 (as history).
      context dLWW `shouldBe` mkVersionVector (Map.fromList [("A", 2), ("B", 1)])

  describe "DVV QuickCheck Properties" $ do
    it "sync is idempotent: sync d d == d (semantically)" $
      property $ \(d :: DVV ID Value) ->
        let synced = sync d d
         in (values synced, context synced) `shouldBe` (values d, context d)

    it "sync is commutative: sync d1 d2 == sync d2 d1" $
      property $ \(d1 :: DVV ID Value) (d2 :: DVV ID Value) ->
        sync d1 d2 `shouldBe` sync d2 d1

    it "sync is associative: sync (sync d1 d2) d3 == sync d1 (sync d2 d3)" $
      property $ \(d1 :: DVV ID Value) (d2 :: DVV ID Value) (d3 :: DVV ID Value) ->
        sync (sync d1 d2) d3 `shouldBe` sync d1 (sync d2 d3)

    it "sync with EmptyDVV is identity: sync EmptyDVV d == d" $
      property $ \(d :: DVV ID Value) ->
        sync EmptyDVV d `shouldBe` d

    it "context is monotonic after sync: context d1 <= context (sync d1 d2)" $
      property $ \(d1 :: DVV ID Value) (d2 :: DVV ID Value) ->
        let ctx1 = context d1
            ctxSync = context (sync d1 d2)
         in all
              (\(k, v) -> Map.lookup k (getVersionVectorCounts ctxSync) >= Just v)
              (Map.toList (getVersionVectorCounts ctx1))

    it "event increases context counter for the actor" $
      property $ \(d :: DVV ID Value) (actor :: ID) (val :: Value) ->
        let ctx = context d
            d' = event d (Just ctx) actor val
            ctx' = context d'
            oldCount = Map.findWithDefault 0 actor (getVersionVectorCounts ctx)
            newCount = Map.findWithDefault 0 actor (getVersionVectorCounts ctx')
         in newCount `shouldBe` (oldCount + 1)

    it "event with full context produces exactly one value" $
      property $ \(d :: DVV ID Value) (actor :: ID) (val :: Value) ->
        let ctx = context d
            d' = event d (Just ctx) actor val
         in size d' `shouldBe` 1

    it "values are preserved or superseded after sync" $
      property $ \(d1 :: DVV ID Value) (d2 :: DVV ID Value) ->
        let synced = sync d1 d2
         in size synced <= size d1 + size d2

    it "prune removes only old history, not active values" $
      property $ \(d :: DVV ID Value) (threshold :: Count) ->
        let pruned = prune threshold d
         in values pruned `shouldBe` values d

    it "reconcile reduces siblings to one value" $
      property $ \(d :: DVV ID Value) (actor :: ID) ->
        let reconciled = reconcile (++) actor d
         in size reconciled <= 1

    it "lww reduces siblings to one value" $
      property $ \(d :: DVV ID Value) (actor :: ID) ->
        let resolved = lww compare actor d
         in size resolved <= 1

    it "context contains all actor IDs from values" $
      property $ \(d :: DVV ID Value) ->
        case d of
          EmptyDVV -> True
          SingletonDVV actor _ -> Map.member actor (getVersionVectorCounts (context d))
          DVV _ vals ->
            let ctx = getVersionVectorCounts (context d)
                actors = [actor | Dot actor _ <- Map.keys vals]
             in all (`Map.member` ctx) actors

    describe "PartialOrd and Ord Properties" $ do
      it "Dot PartialOrd is only defined for same actor" $ do
        let d1 = Dot "A" 10 :: Dot ID
            d2 = Dot "B" 10 :: Dot ID
            d3 = Dot "A" 11 :: Dot ID
        comparable d1 d2 `shouldBe` False
        leq d1 d3 `shouldBe` True
        leq d3 d1 `shouldBe` False

      it "DVV PartialOrd follows causality (happensBefore)" $ do
        let d1 = SingletonDVV "A" "v1" :: DVV ID Value
            d2 = event d1 (Just $ context d1) "A" "v2"
            d3 = SingletonDVV "B" "v3" :: DVV ID Value
        leq d1 d2 `shouldBe` True
        leq d2 d1 `shouldBe` False
        comparable d1 d3 `shouldBe` False -- incomparable
      it "DVV Ord is consistent with PartialOrd" $
        property $ \(d1 :: DVV ID Value) (d2 :: DVV ID Value) ->
          if leq d1 d2
            then if d1 == d2 then compare d1 d2 == EQ else compare d1 d2 == LT
            else
              if leq d2 d1
                then compare d1 d2 == GT
                else compare d1 d2 /= EQ

      it "Replicates Erlang less_test scenarios" $ do
        -- A  = update(new_list(v1),[a]),
        let a = SingletonDVV "a" "v1" :: DVV ID Value
        let ctxA = context a

        -- B  = update(new_list(join(A),[v2]), a),
        -- Effectively: event on A (to get context) with "a" -> "v2"
        let b = event a (Just ctxA) "a" "v2"

        -- B2 = update(new_list(join(A),[v2]), b),
        -- Event on A, actor "b"
        let b2 = event a (Just ctxA) "b" "v2"

        -- B3 = update(new_list(join(A),[v2]), z),
        -- Event on A, actor "z"
        let b3 = event a (Just ctxA) "z" "v2"

        -- C  = update(new_list(join(B),[v3]), A, c),
        let ctxB = context b
        let c = event b (Just ctxB) "c" "v3"

        -- D  = update(new_list(join(C),[v4]), B2, d),
        -- Base is C's context. Update with actor "d". Context B2.
        -- C has {a:2, c:1}. B2 has {a:1, b:1}.
        -- C does not know b:1.
        -- B2 knows b:1.
        -- New DVV will merge contexts: {a:2, b:1, c:1}.
        -- Value v4 (d:1).
        -- Supersedes values in C and B2?
        -- C vals: {a:2, c:1} (if dots kept). v3.
        -- B2 vals: {b:1} v2.
        -- New val: v4 (d:1).
        -- Contexts merged.
        -- Check if v3 (c:1) is superseded by {a:2, b:1, c:1} + d:1?
        -- c:1 is in context. Yes.
        -- v2 (b:1) is in context. Yes.
        -- So D should have only v4.

        -- We construct D by simulating this "update from C base with B2 context":
        -- We assume we start with C (as it provides the base history 'join(C)').
        -- But we add B2's context.
        let ctxB2 = context b2
        let d = event c (Just ctxB2) "d" "v4"
        -- event merges ctxB2 into C's history.
        -- currentMax for "d" in C is 0. Next 1.
        -- Result DVV history: union(C, B2) = {a:2, b:1, c:1, d:1}.
        -- Values: v4.

        -- Assertions
        -- less(A, B) -> A <= B and A != B.
        leq a b `shouldBe` True
        a /= b `shouldBe` True

        -- less(A, C)
        leq a c `shouldBe` True
        a /= c `shouldBe` True

        -- less(B, C)
        leq b c `shouldBe` True
        b /= c `shouldBe` True

        -- less(B, D)
        leq b d `shouldBe` True
        b /= d `shouldBe` True

        -- less(B2, D)
        leq b2 d `shouldBe` True
        b2 /= d `shouldBe` True

        -- less(A, D)
        leq a d `shouldBe` True
        a /= d `shouldBe` True

        -- not less(B2, C) -> B2 not <= C
        leq b2 c `shouldBe` False

        -- not less(B, B2)
        leq b b2 `shouldBe` False

        -- not less(B2, B)
        leq b2 b `shouldBe` False

        -- not less(A, A) (strict) -> leq is True, but Eq.
        -- Erlang less is strict.
        leq a a `shouldBe` True

        -- not less(C, C)
        leq c c `shouldBe` True

        -- not less(D, B2)
        leq d b2 `shouldBe` False

        -- not less(B3, D)
        -- B3 {a:1, z:1}. D {a:2, b:1, c:1, d:1}.
        -- D does NOT know z:1.
        -- So B3 not <= D.
        leq b3 d `shouldBe` False

-- QuickCheck Arbitrary instances

instance
  (Arbitrary actorID, Hashable actorID, Arbitrary value) =>
  Arbitrary (DVV actorID value)
  where
  arbitrary = sized $ \n -> do
    if n <= 0
      then pure EmptyDVV
      else
        frequency
          [ (1, pure EmptyDVV)
          , (3, SingletonDVV <$> arbitrary <*> arbitrary)
          , (2, arbitraryDVV)
          ]
   where
    arbitraryDVV = do
      numActors <- chooseInt (1, 5)
      actors <- vectorOf numActors arbitrary
      -- Build up a DVV through events
      let base = EmptyDVV
      foldM addEvent base actors

    addEvent d actor = do
      val <- arbitrary
      let ctx = context d
      pure $ event d (Just ctx) actor val

  shrink EmptyDVV = []
  shrink (SingletonDVV _ _) = [EmptyDVV]
  shrink (DVV _ vals)
    | Map.null vals = [EmptyDVV]
    | otherwise =
        EmptyDVV : [SingletonDVV actor val | (Dot actor _, val) <- Map.toList vals]
