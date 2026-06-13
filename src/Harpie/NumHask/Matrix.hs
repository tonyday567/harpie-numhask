{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

-- | Square typed-array matrices and the Kleene-star eliminator.
--
-- This module grafts the semiring carriers from "NumHask.Free.Matrix" onto
-- "Harpie.Fixed" arrays and provides an @O(n³)@ one-state elimination
-- algorithm for 'P.StarSemiring'.
module Harpie.NumHask.Matrix
  ( -- * Kleene star on typed arrays
    starMatrix,

    -- * Semiring carriers (re-exported from "NumHask.Free.Matrix")
    Warshall (..),
    MinPlus (..),
    FieldStar (..),
  )
where

import GHC.TypeNats (KnownNat)
import Harpie.Fixed as F hiding (Matrix)
import Harpie.Shape (KnownNats)
import Harpie.Shape qualified as S
import NumHask.Free.Matrix (FieldStar (..), MinPlus (..), Warshall (..))
import NumHask.Prelude as P hiding (Min, cycle, diff, drop, empty, find, length, repeat, sequence, take, zipWith)

type Matrix m n a = F.Array '[m, n] a

-- | Kleene star of a square typed-array matrix by one-state elimination.
--
-- For a carrier @a@, this computes the matrix solution to
-- @star m = 1 + m * star m@.
--
-- === Warshall ('Warshall') — transitive closure
--
-- >>> import Harpie.Fixed (array)
-- >>> import Harpie.NumHask.Matrix
-- >>> let m = array @[2,2] [Warshall False, Warshall True, Warshall False, Warshall False]
-- >>> pretty (starMatrix m)
-- [[Warshall True,Warshall True],
--  [Warshall False,Warshall True]]
--
-- === Floyd–Warshall ('MinPlus') — shortest paths
--
-- >>> let inf = MinPlus (1 P./ 0)
-- >>> let m = array @[3,3] [MinPlus 0, MinPlus 3, inf, inf, MinPlus 0, MinPlus 1, MinPlus 2, inf, MinPlus 0]
-- >>> pretty (starMatrix m)
-- [[MinPlus 0.0,MinPlus 3.0,MinPlus 4.0],
--  [MinPlus 3.0,MinPlus 0.0,MinPlus 1.0],
--  [MinPlus 2.0,MinPlus 5.0,MinPlus 0.0]]
--
-- === Matrix inversion ('FieldStar') — @(I − A)⁻¹@
--
-- >>> let m = array @[2,2] [FieldStar 0.1, FieldStar 0.2, FieldStar 0.3, FieldStar 0.1]
-- >>> pretty (fmap unFieldStar (starMatrix m))
-- [[1.2000000000000002,0.2666666666666667],
--  [0.4000000000000001,1.2000000000000002]]
starMatrix ::
  forall n a.
  ( P.StarSemiring a,
    P.Subtractive a,
    P.Distributive a,
    KnownNat n,
    KnownNats '[n, n],
    P.Additive (Matrix n n a),
    P.Multiplicative (Matrix n n a)
  ) =>
  Matrix n n a ->
  Matrix n n a
starMatrix m
  | dim <= 1 = P.star <$> m
  | otherwise = P.one + go m 0
  where
    dim = S.valueOf @n
    go a k
      | k >= dim = a
      | otherwise =
          let akk = F.index a (S.UnsafeFins [k, k])
              akkStar = P.star akk
              a' =
                F.unsafeTabulate @'[n, n] $ \ij ->
                  case ij of
                    [i, j] ->
                      let aij = F.index a (S.UnsafeFins [i, j])
                          aik = F.index a (S.UnsafeFins [i, k])
                          akj = F.index a (S.UnsafeFins [k, j])
                       in aij + aik * akkStar * akj
                    _ -> P.error "starMatrix: expected exactly two indices"
           in go a' (k + 1)

instance
  ( P.StarSemiring a,
    P.Subtractive a,
    P.Distributive a,
    KnownNat m,
    KnownNats '[m, m],
    P.Additive (Matrix m m a),
    P.Multiplicative (Matrix m m a)
  ) =>
  P.StarSemiring (Matrix m m a)
  where
  star = starMatrix
