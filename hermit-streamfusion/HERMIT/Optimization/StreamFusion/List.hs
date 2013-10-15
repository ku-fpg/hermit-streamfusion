{-# LANGUAGE ExistentialQuantification, BangPatterns #-}
module HERMIT.Optimization.StreamFusion.List
    ( module HERMIT.Optimization.StreamFusion.Base
    , allS
    , andS
    , anyS
    , appendS
    , concatMapS
    , concatS
    , consS
    , dropS
    , elemS
    , enumFromToS
    , filterS
    , flatten
    , flattenS
    , foldlS
    , foldlS'
    , foldrS
    , headS
    , intersperseS
    , iterateS
    , lengthS
    , mapS
    , nilS
    , nubS
    , nullS
    , orS
    , singletonS
    , snocS
    , tailS
    , takeS
    , unfoldrS
    , zipS
    , zipWithS
    ) where

import HERMIT.Optimization.StreamFusion.Base

import Data.Char (ord,chr)
import Data.List (foldl', intersperse, nub, unfoldr)

{-# INLINE allS #-}
allS :: (a -> Bool) -> Stream a -> Bool
allS p (Stream g s) = loop_all s
    where loop_all s = case g s of
                        Done -> True
                        Skip s' -> loop_all s'
                        Yield x s' | p x       -> loop_all s'
                                   | otherwise -> False
          {-# INLINE loop_all #-}
{-# RULES "allS" forall p. all p = allS p . stream #-}

{-# INLINE andS #-}
andS :: Stream Bool -> Bool
andS = foldrS (&&) True
{-# RULES "andS" and = andS . stream #-}

{-# INLINE anyS #-}
anyS :: (a -> Bool) -> Stream a -> Bool
anyS p (Stream g s) = loop_any s
  where loop_any s = case g s of
                        Done -> False
                        Skip s' -> loop_any s'
                        Yield x s' | p x       -> True
                                   | otherwise -> loop_any s'
        {-# INLINE loop_any #-}
{-# RULES "anyS" forall p. any p = anyS p . stream #-}

{-# INLINE appendS #-}
appendS :: Stream a -> Stream a -> Stream a
appendS (Stream n1 s1) (Stream n2 s2) = Stream n (Left s1)
    where n (Left s1) = case n1 s1 of
                            Done -> Skip (Right s2)
                            Skip s1' -> Skip (Left s1')
                            Yield x s1' -> Yield x (Left s1')
          n (Right s2) = case n2 s2 of
                            Done -> Done
                            Skip s2' -> Skip (Right s2')
                            Yield x s2' -> Yield x (Right s2')
          {-# INLINE n #-}
{-# RULES "appendS" forall xs ys. xs ++ ys = unstream (appendS (stream xs) (stream ys)) #-}

{-# INLINE [0] concatS #-}
concatS :: Stream [a] -> [a]
concatS (Stream g s) = loop_concat s
    where loop_concat s = case g s of
                            Done -> []
                            Skip s' -> loop_concat s'
                            Yield xs s' -> loop_concat_inner xs s'
          loop_concat_inner [] s = loop_concat s
          loop_concat_inner (x:xs) s = x : loop_concat_inner xs s
{-# RULES "concatS" forall s. concat (unstream s) = concatS s #-}

{-# INLINE [0] concatMapS #-}
concatMapS :: (a -> Stream b) -> Stream a -> Stream b
concatMapS f (Stream n s) = Stream n' (s, Nothing)
    where n' (s, Nothing) = case n s of
                                Done -> Done
                                Skip s' -> Skip (s', Nothing)
                                Yield x s' -> Skip (s', Just (f x))
          n' (s, Just (Stream n'' s'')) = case n'' s'' of
                                            Done -> Skip (s, Nothing)
                                            Skip s' -> Skip (s, Just (Stream n'' s'))
                                            Yield x s' -> Yield x (s, Just (Stream n'' s'))
          {-# INLINE n' #-}
{-# RULES
"concatMapS" forall f. concatMap f = unstream . concatMapS (stream . f) . stream
"concat/concatMap" forall f xs. concat (map f xs) = concatMap f xs
"concat/concatMapS" forall f. concat . unstream . mapS f = unstream . concatMapS (stream . f)
  #-}

{-# INLINE consS #-}
consS :: a -> Stream a -> Stream a
consS x (Stream n s) = Stream n' (Left s)
    where n' (Left s) = Yield x (Right s)
          n' (Right s) = case n s of
                            Done -> Done
                            Skip s' -> Skip (Right s')
                            Yield x s' -> Yield x (Right s')
          {-# INLINE n' #-}
-- Note: this RULE must never run during or after a phase where unstream
-- is inlinable, or programs will diverge.
-- {-# RULES "consS" [~0] forall x xs. (:) x xs = unstream (consS x (stream xs)) #-}
{-# RULES "consS" forall x xs. stream (x : xs) = consS x (stream xs) #-}

{-# INLINE dropS #-}
dropS :: Int -> Stream a -> Stream a
dropS n (Stream g s) = Stream dropG (Just (max 0 n), s)
    where dropG (Just !n, s)
            | n == 0    = Skip (Nothing, s)
            | otherwise = case g s of
                            Done       -> Done
                            Skip    s' -> Skip (Just n, s')
                            Yield _ s' -> Skip (Just (n-1), s')
          dropG (Nothing, s) = case g s of
                                Done       -> Done
                                Skip    s' -> Skip    (Nothing, s')
                                Yield x s' -> Yield x (Nothing, s')
          {-# INLINE dropG #-}
{-# RULES "dropS" forall n. drop n = unstream . dropS n . stream #-}

{-# INLINE elemS #-}
elemS :: Eq a => a -> Stream a -> Bool
elemS x (Stream g s) = loop_elem s
  where loop_elem s = case g s of
            Done       -> False
            Skip    s' -> loop_elem s'
            Yield y s' | x == y    -> True
                       | otherwise -> loop_elem s'
{-# RULES "elemS" forall x. elem x = elemS x . stream #-}

{-# INLINE enumFromToS #-}
enumFromToS :: Enum a => a -> a -> Stream a
enumFromToS l h = Stream gEnum sEnum
    where {-# INLINE gEnum #-}
          gEnum s | s > fromEnum h = Done
                  | otherwise      = Yield (toEnum s) (s+1)
          sEnum = fromEnum l
          {-# INLINE sEnum #-}
{-# RULES "enumFromToS" forall l. enumFromTo l = unstream . enumFromToS l #-}

{-# INLINE filterS #-}
filterS :: (a -> Bool) -> Stream a -> Stream a
filterS p (Stream n s) = Stream n' s
    where n' s = case n s of
                    Done -> Done
                    Skip s' -> Skip s'
                    Yield x s' | p x -> Yield x s'
                               | otherwise -> Skip s'
{-# RULES "filterS" forall p. filter p = unstream . filterS p . stream #-}

{-# INLINE flatten #-}
flatten :: forall a b s. (a -> s) -> (s -> Step b s) -> [a] -> [b]
flatten mk gFlatten = unstream . flattenS mk gFlatten . stream

{-# INLINE flattenS #-}
flattenS :: forall a b s. (a -> s) -> (s -> Step b s) -> Stream a -> Stream b
flattenS mk gFlatten (Stream n s) = Stream n' sFlatten
    where n' (s, Nothing) = case n s of
                                    Done -> Done
                                    Skip s' -> Skip (s', Nothing)
                                    Yield x s' -> Skip (s', Just (mk x))
          n' (s, Just s'') = case gFlatten s'' of
                                    Done -> Skip (s, Nothing)
                                    Skip s' -> Skip (s, Just s')
                                    Yield x s' -> Yield x (s, Just s')
          {-# INLINE n' #-}
          sFlatten = (s, Nothing)
          {-# INLINE sFlatten #-}

{-# INLINE foldlS #-}
foldlS :: (b -> a -> b) -> b -> Stream a -> b
foldlS f z (Stream n s) = go SPEC z s
    where go !sPEC z s = case n s of
                            Done       -> z
                            Skip s'    -> go sPEC z s'
                            Yield x s' -> go sPEC (f z x) s'
{-# RULES "foldlS" forall f z. foldl f z = foldlS f z . stream #-}

{-# INLINE foldlS' #-}
foldlS' :: (b -> a -> b) -> b -> Stream a -> b
foldlS' f z (Stream n s) = go SPEC z s
    where go !sPEC !z !s = case n s of
                            Done       -> z
                            Skip s'    -> go sPEC z s'
                            Yield x s' -> go sPEC (f z x) s'
{-# RULES "foldlS'" forall f z. foldl' f z = foldlS' f z . stream #-}
{-# RULES "sum" sum = foldl' (+) 0 #-}
{-# RULES "product" product = foldl' (*) 1 #-}

{-# INLINE foldrS #-}
foldrS :: (a -> b -> b) -> b -> Stream a -> b
foldrS f z (Stream n s) = go SPEC s
    where go !sPEC s = case n s of
                        Done       -> z
                        Skip s'    -> go sPEC s'
                        Yield x s' -> f x (go sPEC s')
{-# RULES "foldrS" forall f z. foldr f z = foldrS f z . stream #-}

{-# INLINE headS #-}
headS :: Stream a -> a
headS (Stream n s) = go SPEC s
    where go !sPEC s = case n s of
                        Done -> error "headS empty stream"
                        Skip s' -> go sPEC s'
                        Yield x _ -> x
{-# RULES "headS" head = headS . stream #-}

{-# INLINE intersperseS #-}
intersperseS :: a -> Stream a -> Stream a
intersperseS sep (Stream g s) = Stream intersperseG (Left s, Nothing)
  where intersperseG (Left s, Nothing) = case g s of
            Done       -> Done
            Skip    s' -> Skip (Left s', Nothing)
            Yield x s' -> Skip (Left s', Just x)

        intersperseG (Left s, Just x) = Yield x (Right s, Nothing)

        intersperseG (Right s, Nothing) = case g s of
            Done       -> Done
            Skip    s' -> Skip      (Right s', Nothing)
            Yield x s' -> Yield sep (Left s', Just x)
        -- intersperseG (Right _, Just _) -- can't happen
        {-# INLINE intersperseG #-}
{-# RULES "intersperseS" forall p. intersperse p = unstream . intersperseS p . stream #-}

{-# INLINE iterateS #-}
iterateS :: (a -> a) -> a -> Stream a
iterateS f x = Stream n x
    where n x = Yield x (f x)
          {-# INLINE n #-}
{-# RULES "iterateS" forall f. iterate f = unstream . iterateS f #-}

{-# INLINE lengthS #-}
lengthS :: Stream a -> Int
lengthS = foldlS' (\s _ -> s + 1) (0 :: Int)
{-# RULES "lengthS" length = lengthS . stream #-}

{-# INLINE mapS #-}
mapS :: (a -> b) -> Stream a -> Stream b
mapS f (Stream n s) = Stream n' s
    where n' s = case n s of
                    Done       -> Done
                    Skip s'    -> Skip s'
                    Yield x s' -> Yield (f x) s'
          {-# INLINE n' #-}
{-# RULES "mapS" forall f. map f = unstream . mapS f . stream #-}

{-# INLINE nilS #-}
nilS :: Stream a
nilS = Stream (\() -> Done) ()
{-# RULES "nilS" stream [] = nilS #-}

{-# INLINE nubS #-}
nubS :: Eq a => Stream a -> Stream a
nubS (Stream g s) = Stream nubG ([],s)
    where nubG (seen,s) = case g s of
                            Done -> Done
                            Skip s' -> Skip (seen,s')
                            Yield x s' | x `elem` seen -> Skip (seen, s')
                                       | otherwise -> Yield x (x:seen, s')
          {-# INLINE nubG #-}
{-# RULES "nubS" nub = unstream . nubS . stream #-}

{-# INLINE nullS #-}
nullS :: Stream a -> Bool
nullS (Stream g s) = loop_null s
  where loop_null s = case g s of
            Done       -> True
            Skip    s' -> loop_null s'
            Yield _ _  -> False
{-# RULES "nullS" null = nullS . stream #-}

{-# INLINE orS #-}
orS :: Stream Bool -> Bool
orS = foldrS (||) False
{-# RULES "orS" or = orS . stream #-}

{-# INLINE singletonS #-}
singletonS :: a -> Stream a
singletonS x = Stream n (Just x)
    where n (Just x) = Yield x Nothing
          n Nothing  = Done
          {-# INLINE n #-}
-- {-# RULES "singletonS" forall x. consS x nilS = singletonS x #-}
{-# RULES "singletonS" forall x. (:) x [] = unstream (singletonS x) #-}
-- evaluated
-- {-# RULES "singletonS" forall x. stream [x] = singletonS x #-}
-- seems slower
-- Goal: prevent CAF lists from getting pointlessly turned into consS and singletonS

{-# INLINE snocS #-}
snocS :: Stream a -> a -> Stream a
snocS (Stream g s) y = Stream snocG (Just s)
  where snocG (Just xs) = case g s of
                            Done       -> Yield y Nothing
                            Skip s'    -> Skip    (Just s')
                            Yield x s' -> Yield x (Just s')
        snocG Nothing = Done
        {-# INLINE snocG #-}
{-# RULES "snocS" forall l x. l ++ [x] = unstream (snocS (stream l) x) #-}

{-# INLINE tailS #-}
tailS :: Stream a -> Stream a
tailS (Stream n s) = Stream n' (Left s)
    where n' (Left s) = case n s of
                            Done -> error "tailS empty stream"
                            Skip s' -> Skip (Left s')
                            Yield _ s' -> Skip (Right s')
          n' (Right s) = case n s of
                            Done -> Done
                            Skip s' -> Skip (Right s')
                            Yield x s' -> Yield x (Right s')
          {-# INLINE n' #-}
{-# RULES "tailS" tail = unstream . tailS . stream #-}

{-# INLINE takeS #-}
takeS :: Int -> Stream a -> Stream a
takeS n (Stream g s) = Stream takeG (n,s)
  where takeG (!n, s)
            | n > 0 = case g s of
                        Done       -> Done
                        Skip    s' -> Skip    (n, s')
                        Yield x s' -> Yield x (n-1, s')
            | otherwise = Done
        {-# INLINE takeG #-}
{-# RULES "takeS" forall n. take n = unstream . takeS n . stream #-}

{-# INLINE unfoldrS #-}
unfoldrS :: (b -> Maybe (a, b)) -> b -> Stream a
unfoldrS f s = Stream unfoldrG s
    where unfoldrG s = case f s of
                        Nothing      -> Done
                        Just (x, s') -> Yield x s'
          {-# INLINE unfoldrG #-}
{-# RULES "unfoldrS" forall f s. unfoldr f s = unstream (unfoldrS f s) #-}

{-# INLINE zipS #-}
zipS :: Stream a -> Stream b -> Stream (a,b)
zipS = zipWithS (,)
{-# RULES "zipS" forall xs. zip xs = unstream . zipS (stream xs) . stream #-}

{-# INLINE zipWithS #-}
zipWithS :: (a -> b -> c) -> Stream a -> Stream b -> Stream c
zipWithS f (Stream na sa) (Stream nb sb) = Stream n (sa, sb, Nothing)
    where n (sa, sb, Nothing) = case na sa of
                                    Done -> Done
                                    Skip sa' -> Skip (sa', sb, Nothing)
                                    Yield a sa' -> Skip (sa', sb, Just a)
          n (sa, sb, Just a) = case nb sb of
                                    Done -> Done
                                    Skip sb' -> Skip (sa, sb', Just a)
                                    Yield b sb' -> Yield (f a b) (sa, sb', Nothing)
          {-# INLINE n #-}
{-# RULES "zipWithS" forall f xs. zipWith f xs = unstream . zipWithS f (stream xs) . stream #-}

{-
--    -- * Basic stream functions
--    append1,                 -- :: Stream a -> [a] -> [a]
--    cons,                   -- :: a -> Stream a -> Stream a
--    snoc,                   -- :: Stream a -> a -> Stream a
--    head,                   -- :: Stream a -> a
--    last,                   -- :: Stream a -> a
--    tail,                   -- :: Stream a -> Stream a
--    init,                   -- :: Stream a -> Stream a

--  intercalate,          -- :: Stream a -> Stream (Stream a) -> Stream a
--  transpose,              -- :: Stream (Stream a) -> Stream (Stream a)

--    foldl1,                 -- :: (a -> a -> a) -> Stream a -> a
--    foldl1',                -- :: (a -> a -> a) -> Stream a -> a
--    foldr,                  -- :: (a -> b -> b) -> b -> Stream a -> b
 --   foldr1,                 -- :: (a -> a -> a) -> Stream a -> a

--    maximum,                -- :: Ord a => Stream a -> a
--    minimum,                -- :: Ord a => Stream a -> a
--    strictMaximum,          -- :: Ord a => Stream a -> a
--    strictMinimum,          -- :: Ord a => Stream a -> a

--    scanl,                  -- :: (a -> b -> a) -> a -> Stream b -> Stream a
--    scanl1,                 -- :: (a -> a -> a) -> Stream a -> Stream a
--    scanr,                  -- :: (a -> b -> b) -> b -> Stream a -> Stream b
--    scanr1,                 -- :: (a -> a -> a) -> Stream a -> Stream a

--    mapAccumL,              -- :: (acc -> x -> (acc, y)) -> acc -> Stream x -> (acc, Stream y)
--    mapAccumR,              -- :: (acc -> x -> (acc, y)) -> acc -> Stream x -> (acc, Stream y)

--    repeat,                 -- :: a -> Stream a
--    replicate,              -- :: Int -> a -> Stream a
--    cycle,                  -- :: Stream a -> Stream a

--    unfoldr,                -- :: (b -> Maybe (a, b)) -> b -> Stream a

--    splitAt,                -- :: Int -> Stream a -> ([a], [a])
--    takeWhile,              -- :: (a -> Bool) -> Stream a -> Stream a
--    dropWhile,              -- :: (a -> Bool) -> Stream a -> Stream a
--    span,                   -- :: (a -> Bool) -> Stream a -> (Stream a, Stream a)
--    break,                  -- :: (a -> Bool) -> Stream a -> (Stream a, Stream a)
--    group,                  -- :: Eq a => Stream a -> Stream (Stream a)
--    inits,                  -- :: Stream a -> Stream (Stream a)
--    tails,                  -- :: Stream a -> Stream (Stream a)

--    isPrefixOf,             -- :: Eq a => Stream a -> Stream a -> Bool
--    isSuffixOf,             -- :: Eq a => Stream a -> Stream a -> Bool
--    isInfixOf,              -- :: Eq a => Stream a -> Stream a -> Bool

--    elem,                   -- :: Eq a => a -> Stream a -> Bool
--    lookup,                 -- :: Eq a => a -> Stream (a, b) -> Maybe b

--    find,                   -- :: (a -> Bool) -> Stream a -> Maybe a
--    filter,                 -- :: (a -> Bool) -> Stream a -> Stream a
--  partition,              -- :: (a -> Bool) -> Stream a -> ([a], [a])

--    index,                  --  :: Stream a -> Int -> a
--    findIndex,              -- :: (a -> Bool) -> Stream a -> Maybe Int
--    elemIndex,              -- :: Eq a => a -> Stream a -> Maybe Int
--    elemIndices,            -- :: Eq a => a -> Stream a -> Stream Int
--    findIndices,            -- :: (a -> Bool) -> Stream a -> Stream Int

--    zip,                    -- :: Stream a -> Stream b -> Stream (a, b)
--    zip3,                   -- :: Stream a -> Stream b -> Stream c -> Stream (a, b, c)
--    zip4,
--    zipWith,                -- :: (a -> b -> c) -> Stream a -> Stream b -> Stream c
--    zipWith3,               -- :: (a -> b -> c -> d) -> Stream a -> Stream b -> Stream c -> Stream d
--    zipWith4,

--    zip4, zip5, zip6, zip7,

--    zipWith4, zipWith5, zipWith6, zipWith7,
--    unzip,                  -- :: Stream (a, b) -> (Stream a, Stream b)
--    unzip3,                 -- :: Stream (a, b, c) -> (Stream a, Stream b, Stream c)
--    unzip4, unzip5, unzip6, unzip7,

--    lines,                  -- :: Stream Char -> Stream [Char]
--    unlines,                -- :: Stream (Stream Char) -> Stream Char
--    words,                  -- :: Stream Char -> Stream (Stream Char)
--    unwords,                -- :: Stream (Stream Char) -> Stream Char
--    nub,                    -- :: Eq a => Stream a -> Stream a
--    delete,                 -- :: Eq a => a -> Stream a -> Stream a
--    (\\),                   -- :: Eq a => Stream a -> Stream a -> Stream a
--    union,                  -- :: Eq a => Stream a -> Stream a -> Stream a
--    intersect,              -- :: Eq a => Stream a -> Stream a -> Stream a

--    sort,                   -- :: Ord a => Stream a -> Stream a
--    insert,                 -- :: Ord a => a -> Stream a -> Stream a
--    nubBy,                  -- :: (a -> a -> Bool) -> Stream a -> Stream a
--    deleteBy,               -- :: (a -> a -> Bool) -> a -> Stream a -> Stream a
--    deleteFirstsBy,         -- :: (a -> a -> Bool) -> Stream a -> Stream a -> Stream a
--    unionBy,                -- :: (a -> a -> Bool) -> Stream a -> Stream a -> Stream a
--    intersectBy,            -- :: (a -> a -> Bool) -> Stream a -> Stream a -> Stream a
--    groupBy,                -- :: (a -> a -> Bool) -> Stream a -> Stream (Stream a)
--    insertBy,               -- :: (a -> a -> Ordering) -> a -> Stream a -> Stream a
--    sortBy,                 -- :: (a -> a -> Ordering) -> Stream a -> Stream a
--    maximumBy,              -- :: (a -> a -> Ordering) -> Stream a -> a
--    minimumBy,              -- :: (a -> a -> Ordering) -> Stream a -> a

--    genericLength,          -- :: Num i => Stream b -> i
--    genericTake,            -- :: Integral i => i -> Stream a -> Stream a
--    genericDrop,            -- :: Integral i => i -> Stream a -> Stream a
--    genericIndex,           -- :: Integral a => Stream b -> a -> b
--    genericSplitAt,         -- :: Integral i => i -> Stream a -> ([a], [a])

--    enumFromToInt,          -- :: Int -> Int -> Stream Int
--    enumFromToChar,         -- :: Char -> Char -> Stream Char
--    enumDeltaInteger,       -- :: Integer -> Integer -> Stream Integer

--    foldM,                  -- :: Monad m => (b -> a -> m b) -> b -> Stream a -> m b
--   foldM_,                 -- :: Monad m => (b -> a -> m b) -> b -> Stream a -> m ()

--    return,                 -- :: a -> Stream a
--    guard,                  -- :: Bool -> Stream a -> Stream a
--    bind,                   -- :: (a -> Bool) -> (a -> [b]) -> [a] -> [b]
--    mapFilter,              -- :: (a -> Bool) -> (a ->  b)  -> [a] -> [b]
--    declare                 -- :: (a -> Stream b) -> a -> Stream b
-- ---------------------------------------------------------------------
-- Basic stream functions

-- version that can share the second list arg, really very similar
-- to unstream, but conses onto a given list rather than []:
-- unstream s = append1 s []
--
append1 :: Stream a -> [a] -> [a]
append1 (Stream next s0) xs = loop_append1 s0
  where
    loop_append1 !s = case next s of
      Done       -> xs
      Skip    s' -> expose s'       loop_append1 s'
      Yield x s' -> expose s' $ x : loop_append1 s'
{-# INLINE [0] append1 #-}

-- last
last :: Stream a -> a
last (Stream next s0) = loop0_last s0
  where
    loop0_last !s = case next s of
      Done       -> errorEmptyStream "last"
      Skip    s' -> expose s' $ loop0_last  s'
      Yield x s' -> expose s' $ loop_last x s'
    loop_last x !s = case next s of
      Done        -> x
      Skip     s' -> expose s' $ loop_last x  s'
      Yield x' s' -> expose s' $ loop_last x' s'
{-# INLINE [0] last #-}

-- init
init :: Stream a -> Stream a
init (Stream next0 s0) = Stream next (Nothing :!: s0)
  where
    {-# INLINE next #-}
    next (Nothing :!: s) = case next0 s of
      Done       -> errorEmptyStream "init"
      Skip    s' -> Skip (Nothing    :!: s')
      Yield x s' -> Skip (Just (L x) :!: s')
    next (Just (L x) :!: s) = case next0 s of
      Done        -> Done
      Skip     s' -> Skip    (Just (L x)  :!: s')
      Yield x' s' -> Yield x (Just (L x') :!: s')
{-# INLINE [0] init #-}

-- intercalate :: Stream a -> Stream (Stream a) -> Stream a
-- transpose :: Stream (Stream a) -> Stream (Stream a)

------------------------------------------------------------------------

foldl1 :: (a -> a -> a) -> Stream a -> a
foldl1 f (Stream next s0) = loop0_foldl1 s0
  where
    loop0_foldl1 !s = case next s of
      Skip    s' -> expose s' $ loop0_foldl1 s'
      Yield x s' -> expose s' $ loop_foldl1 x s'
      Done       -> errorEmptyStream "foldl1"

    loop_foldl1 z !s = expose s $ case next s of
      Done       -> z
      Skip    s' -> expose s' $ loop_foldl1 z s'
      Yield x s' -> expose s' $ loop_foldl1 (f z x) s'
{-# INLINE [0] foldl1 #-}

foldl1' :: (a -> a -> a) -> Stream a -> a
foldl1' f (Stream next s0) = loop0_foldl1' s0
  where
    loop0_foldl1' !s = case next s of
      Skip    s' -> expose s' $ loop0_foldl1' s'
      Yield x s' -> expose s' $ loop_foldl1' x s'
      Done       -> errorEmptyStream "foldl1"

    loop_foldl1' !z !s = case next s of
      Done       -> z
      Skip    s' -> expose s' $ loop_foldl1' z s'
      Yield x s' -> expose s' $ loop_foldl1' (f z x) s'
{-# INLINE [0] foldl1' #-}

foldr1 :: (a -> a -> a) -> Stream a -> a
foldr1 f (Stream next s0) = loop0_foldr1 s0
  where
    loop0_foldr1 !s = case next s of
      Done       -> errorEmptyStream "foldr1"
      Skip    s' -> expose s' $ loop0_foldr1  s'
      Yield x s' -> expose s' $ loop_foldr1 x s'

    loop_foldr1 x !s = case next s of
      Done        -> x
      Skip     s' -> expose s' $ loop_foldr1 x s'
      Yield x' s' -> expose s' $ f x (loop_foldr1 x' s')
{-# INLINE [0] foldr1 #-}

------------------------------------------------------------------------
-- ** Special folds

-- concat
--

maximum :: Ord a => Stream a -> a
maximum (Stream next s0) = loop0_maximum s0
  where
    loop0_maximum !s = case next s of
      Done       -> errorEmptyStream "maximum"
      Skip    s' -> expose s' $ loop0_maximum s'
      Yield x s' -> expose s' $ loop_maximum x s'
    loop_maximum z !s = case next s of               -- note, lazy in the accumulator
      Done       -> z
      Skip    s' -> expose s' $ loop_maximum z s'
      Yield x s' -> expose s' $ loop_maximum (max z x) s'
{-# INLINE [0] maximum #-}

{-# RULES
  "maximumInt"     maximum = (strictMaximum :: Stream Int  -> Int);
  "maximumChar"    maximum = (strictMaximum :: Stream Char -> Char)
  #-}

strictMaximum :: Ord a => Stream a -> a
strictMaximum (Stream next s0) = loop0_strictMaximum s0
  where
    loop0_strictMaximum !s = case next s of
      Done       -> errorEmptyStream "maximum"
      Skip    s' -> expose s' $ loop0_strictMaximum s'
      Yield x s' -> expose s' $ loop_strictMaximum x s'
    loop_strictMaximum !z !s = case next s of
      Done       -> z
      Skip    s' -> expose s' $ loop_strictMaximum z s'
      Yield x s' -> expose s' $ loop_strictMaximum (max z x) s'
{-# INLINE [0] strictMaximum #-}

minimum :: Ord a => Stream a -> a
minimum (Stream next s0) = loop0_minimum s0
  where
    loop0_minimum !s = case next s of
      Done       -> errorEmptyStream "minimum"
      Skip    s' -> expose s' $ loop0_minimum s'
      Yield x s' -> expose s' $ loop_minimum x s'
    loop_minimum z !s = case next s of
      Done       -> z
      Skip    s' -> expose s' $ loop_minimum z s'
      Yield x s' -> expose s' $ loop_minimum (min z x) s'
{-# INLINE [0] minimum #-}

{-# RULES
  "minimumInt"     minimum = (strictMinimum :: Stream Int  -> Int);
  "minimumChar"    minimum = (strictMinimum :: Stream Char -> Char)
  #-}

strictMinimum :: Ord a => Stream a -> a
strictMinimum (Stream next s0) = loop0_strictMinimum s0
  where
    loop0_strictMinimum !s = case next s of
      Done       -> errorEmptyStream "minimum"
      Skip    s' -> expose s' $ loop0_strictMinimum s'
      Yield x s' -> expose s' $ loop_strictMinimum x s'
    loop_strictMinimum !z !s = case next s of
      Done       -> z
      Skip    s' -> expose s' $ loop_strictMinimum z s'
      Yield x s' -> expose s' $ loop_strictMinimum (min z x) s'
{-# INLINE [0] strictMinimum #-}

------------------------------------------------------------------------
-- * Building lists
-- ** Scans

--
-- FIXME: not a proper scanl. expects a list one longer than the input list,
-- in order to get the z0th element
--
scanl :: (b -> a -> b) -> b -> Stream a -> Stream b
scanl f z0 (Stream next0 s0) = Stream next (L z0 :!: s0)
  where
    {-# INLINE next #-}
    next (L z :!: s) = case next0 s of
        Done        -> Done
        Skip    s'  -> Skip    (L z       :!: s')
        Yield x s'  -> Yield z (L (f z x) :!: s')
{-# INLINE [0] scanl #-}

scanl1 :: (a -> a -> a) -> Stream a -> Stream a
scanl1 f (Stream next0 s0) = Stream next (Nothing :!: s0)
  where
    {-# INLINE next #-}
    next (Nothing :!: s)      = case next0 s of
            Done       -> Done
            Skip s'    -> Skip (Nothing    :!: s')
            Yield x s' -> Skip (Just (L x) :!: s')
    next (Just (L z) :!: s)   = case next0 s of
        Done       -> Done
        Skip    s' -> Skip    (Just (L z)       :!: s')
        Yield x s' -> Yield z (Just (L (f z x)) :!: s')
{-# INLINE [0] scanl1 #-}

--
-- hmm. hard.
--

{-
scanr :: (b -> a -> b) -> b -> Stream a -> Stream b
scanr f z0 (Stream next s0) = Stream next' (Just s0)
  where
    next' (Just s) = case next s of
        Done        -> Yield z0 (Nothing, s)
        Skip s'     -> Skip (Just s')
        Yield x s'  -> -- hmm.

    next' Nothing = Done
{-# INLINE [0] scanl #-}
-}


{-
scanr :: (a -> b -> b) -> b -> Stream a -> Stream b
scanr f z0 (Stream next s0) = Stream next' (z0, s0)     -- should be using strict pairs??
  where
    next' (z, s) = case next s of
        Done        -> Done
        Skip s'     -> Skip (z, s')
        Yield x s'  -> Yield z (f x z, s') -- flip f
{-# INLINE [0] scanr #-}
-}

{-
scanl1 :: (a -> a -> a) -> Stream a -> Stream a
scanr1 :: (a -> a -> a) -> Stream a -> Stream a
-}

------------------------------------------------------------------------
-- ** Accumulating maps

{-
--
-- not right:
--
mapAccumL :: (acc -> x -> (acc, y)) -> acc -> Stream x -> (acc, Stream y)
mapAccumL f acc (Stream step s) = Stream step' (s, acc)
  where
    step' (s, acc) = case step s of
          Done       -> Done
          Skip s'    -> Skip (s', acc)
          Yield x s' -> let (acc', y) = f acc x in Yield y (s', acc')
{-# INLINE [0] mapAccumL #-}
-}

{-
mapAccumR :: (acc -> x -> (acc, y)) -> acc -> Stream x -> (acc, Stream y)
-}

------------------------------------------------------------------------
-- ** Infinite streams

repeat :: a -> Stream a
repeat x = Stream next None
  where
    {-# INLINE next #-}
    next _ = Yield x None
{-# INLINE [0] repeat #-}

replicate :: Int -> a -> Stream a
replicate n x = Stream next (L n)
  where
    {-# INLINE next #-}
    next (L !i) | i <= 0    = Done
                | otherwise = Yield x (L (i-1))
{-# INLINE [0] replicate #-}

--"reverse/replicate" forall n x. reverse (replicate n x) = replicate n x

cycle :: Stream a -> Stream a
cycle (Stream next0 s0) = Stream next (s0 :!: S1)
  where
    {-# INLINE next #-}
    next (s :!: S1) = case next0 s of
      Done       -> errorEmptyStream "cycle"
      Skip    s' -> Skip    (s' :!: S1)
      Yield x s' -> Yield x (s' :!: S2)
    next (s :!: S2) = case next0 s of
      Done       -> Skip    (s0 :!: S2)
      Skip    s' -> Skip    (s' :!: S2)
      Yield x s' -> Yield x (s' :!: S2)
{-# INLINE [0] cycle #-}

------------------------------------------------------------------------
-- ** Unfolding

------------------------------------------------------------------------
-- * Substreams
-- ** Extracting substreams

--TODO: could perhaps use 0 instead of Nothing, so long as
--      spec constr works with that

splitAt :: Int -> Stream a -> ([a], [a])
splitAt n0 (Stream next s0)
  --TODO: we should not need this special case, (n < 0) should be as
  --      cheap as pattern matching n against 0
  | n0 < 0    = ([], expose s0 $ unstream (Stream next s0))
  | otherwise = loop_splitAt n0 s0
  where
    loop_splitAt  0 !s = ([], expose s $ unstream (Stream next s))
    loop_splitAt !n !s = case next s of
      Done            -> ([], [])
      Skip    s'      -> expose s $ loop_splitAt n s'
      Yield x s'      -> (x:xs', xs'')
        where
          (xs', xs'') = expose s $ loop_splitAt (n-1) s'
{-# INLINE [0] splitAt #-}

takeWhile :: (a -> Bool) -> Stream a -> Stream a
takeWhile p (Stream next0 s0) = Stream next s0
  where
    {-# INLINE next #-}
    next !s = case next0 s of
      Done                   -> Done
      Skip    s'             -> Skip s'
      Yield x s' | p x       -> Yield x s'
                 | otherwise -> Done
{-# INLINE [0] takeWhile #-}

dropWhile :: (a -> Bool) -> Stream a -> Stream a
dropWhile p (Stream next0 s0) = Stream next (S1 :!: s0)
  where
    {-# INLINE next #-}
    next (S1 :!: s)  = case next0 s of
      Done                   -> Done
      Skip    s'             -> Skip    (S1 :!: s')
      Yield x s' | p x       -> Skip    (S1 :!: s')
                 | otherwise -> Yield x (S2 :!: s')
    next (S2 :!: s) = case next0 s of
      Done       -> Done
      Skip    s' -> Skip    (S2 :!: s')
      Yield x s' -> Yield x (S2 :!: s')
{-# INLINE [0] dropWhile #-}

{-
span :: (a -> Bool) -> Stream a -> (Stream a, Stream a)
break :: (a -> Bool) -> Stream a -> (Stream a, Stream a)
group :: Eq a => Stream a -> Stream (Stream a)
inits :: Stream a -> Stream (Stream a)
tails :: Stream a -> Stream (Stream a)
-}

------------------------------------------------------------------------
-- * Predicates

isPrefixOf :: Eq a => Stream a -> Stream a -> Bool
isPrefixOf (Stream stepa sa0) (Stream stepb sb0) = loop_isPrefixOf sa0 sb0 Nothing
  where
    loop_isPrefixOf !sa !sb Nothing = case stepa sa of
        Done        -> True
        Skip    sa' -> expose sa' $ loop_isPrefixOf sa' sb Nothing
        Yield x sa' -> expose sa' $ loop_isPrefixOf sa' sb (Just (L x))

    loop_isPrefixOf !sa !sb (Just (L x)) = case stepb sb of
        Done                    -> False
        Skip    sb'             -> expose sb' $ loop_isPrefixOf sa sb' (Just (L x))
        Yield y sb' | x == y    -> expose sb' $ loop_isPrefixOf sa sb' Nothing
                    | otherwise -> False
{-# INLINE [0] isPrefixOf #-}


{-
isSuffixOf :: Eq a => Stream a -> Stream a -> Bool
isInfixOf :: Eq a => Stream a -> Stream a -> Bool
-}

------------------------------------------------------------------------
-- * Searching streams
-- ** Searching by equality


{-
--
-- No need to provide notElem, as not . elem is just as fusible.
-- You can only fuse on the rhs of elem anyway.
--

notElem :: Eq a => a -> Stream a -> Bool
notElem x (Stream next s0) = loop s0
  where
    loop !s = case next s of
      Done                   -> True
      Skip    s'             -> loop s'
      Yield y s' | x == y    -> False
                 | otherwise -> loop s'
{-# INLINE [0] notElem #-}
-}

lookup :: Eq a => a -> Stream (a, b) -> Data.Maybe.Maybe b
lookup key (Stream next s0) = loop_lookup s0
  where
    loop_lookup !s = case next s of
      Done                        -> Data.Maybe.Nothing
      Skip         s'             -> expose s' $ loop_lookup s'
      Yield (x, y) s' | key == x  -> Data.Maybe.Just y
                      | otherwise -> expose s' $ loop_lookup s'
{-# INLINE [0] lookup #-}

------------------------------------------------------------------------
-- ** Searching with a predicate

find :: (a -> Bool) -> Stream a -> Data.Maybe.Maybe a
find p (Stream next s0) = loop_find s0
  where
    loop_find !s = case next s of
      Done                   -> Data.Maybe.Nothing
      Skip    s'             -> expose s' $ loop_find s'
      Yield x s' | p x       -> Data.Maybe.Just x
                 | otherwise -> expose s' $ loop_find s'
{-# INLINE [0] find #-}

filter :: (a -> Bool) -> Stream a -> Stream a
filter p (Stream next0 s0) = Stream next s0
  where
    {-# INLINE next #-}
    next !s = case next0 s of
      Done                   -> Done
      Skip    s'             -> Skip    s'
      Yield x s' | p x       -> Yield x s'
                 | otherwise -> Skip    s'
{-# INLINE [0] filter #-}

{-# RULES
    "Stream filter/filter fusion" forall p q s.
        filter p (filter q s) = filter (\x -> q x && p x) s
 #-}

--partition :: (a -> Bool) -> Stream a -> (Stream a, Stream a)

------------------------------------------------------------------------
-- * Indexing streams

index :: Stream a -> Int -> a
index (Stream next s0) n0
  | n0 < 0    = error "Stream.(!!): negative index"
  | otherwise = loop_index n0 s0
  where
    loop_index !n !s = case next s of
      Done                   -> error "Stream.(!!): index too large"
      Skip    s'             -> expose s' $ loop_index  n    s'
      Yield x s' | n == 0    -> x
                 | otherwise -> expose s' $ loop_index (n-1) s'
{-# INLINE [0] index #-}

findIndex :: (a -> Bool) -> Stream a -> Data.Maybe.Maybe Int
findIndex p (Stream next s0) = loop_findIndex 0 s0
  where
    loop_findIndex !i !s = case next s of
      Done                   -> Data.Maybe.Nothing
      Skip    s'             -> expose s' $ loop_findIndex i     s' -- hmm. not caught by QC
      Yield x s' | p x       -> Data.Maybe.Just i
                 | otherwise -> expose s' $ loop_findIndex (i+1) s'
{-# INLINE [0] findIndex #-}

elemIndex :: Eq a => a -> Stream a -> Data.Maybe.Maybe Int
elemIndex a (Stream next s0) = loop_elemIndex 0 s0
  where
    loop_elemIndex !i !s = case next s of
      Done                   -> Data.Maybe.Nothing
      Skip    s'             -> expose s' $ loop_elemIndex i     s'
      Yield x s' | a == x    -> Data.Maybe.Just i
                 | otherwise -> expose s' $ loop_elemIndex (i+1) s'
{-# INLINE [0] elemIndex #-}

elemIndices :: Eq a => a -> Stream a -> Stream Int
elemIndices a (Stream next0 s0) = Stream next (S 0 :!: s0)
  where
    {-# INLINE next #-}
    next (S n :!: s) = case next0 s of
        Done                   -> Done
        Skip    s'             -> Skip    (S n     :!: s')
        Yield x s' | x == a    -> Yield n (S (n+1) :!: s')
                   | otherwise -> Skip    (S (n+1) :!: s')
{-# INLINE [0] elemIndices #-}

findIndices :: (a -> Bool) -> Stream a -> Stream Int
findIndices p (Stream next0 s0) = Stream next (S 0 :!: s0)
  where
    {-# INLINE next #-}
    next (S n :!: s) = case next0 s of
        Done                   -> Done
        Skip    s'             -> Skip    (S n     :!: s')
        Yield x s' | p x       -> Yield n (S (n+1) :!: s')
                   | otherwise -> Skip    (S (n+1) :!: s')
{-# INLINE [0] findIndices #-}

------------------------------------------------------------------------
-- * Zipping and unzipping streams

zip :: Stream a -> Stream b -> Stream (a, b)
zip = zipWith (,)
{-# INLINE zip #-}

zip3 :: Stream a -> Stream b -> Stream c -> Stream (a, b, c)
zip3 = zipWith3 (,,)
{-# INLINE zip3 #-}

zip4 :: Stream a -> Stream b -> Stream c -> Stream d -> Stream (a, b, c, d)
zip4 = zipWith4 (,,,)
{-# INLINE zip4 #-}

{-
zip5 :: Stream a -> Stream b -> Stream c -> Stream d -> Stream e -> [(a, b, c, d, e)]
zip6 :: Stream a -> Stream b -> Stream c -> Stream d -> Stream e -> Stream f -> [(a, b, c, d, e, f)]
zip7 :: Stream a -> Stream b -> Stream c -> Stream d -> Stream e -> Stream f -> Stream g -> [(a, b, c, d, e, f, g)]
-}

zipWith :: (a -> b -> c) -> Stream a -> Stream b -> Stream c
zipWith f (Stream next0 sa0) (Stream next1 sb0) = Stream next (sa0 :!: sb0 :!: Nothing)
  where
    {-# INLINE next #-}
    next (sa :!: sb :!: Nothing)     = case next0 sa of
        Done        -> Done
        Skip    sa' -> Skip (sa' :!: sb :!: Nothing)
        Yield a sa' -> Skip (sa' :!: sb :!: Just (L a))

    next (sa' :!: sb :!: Just (L a)) = case next1 sb of
        Done        -> Done
        Skip    sb' -> Skip          (sa' :!: sb' :!: Just (L a))
        Yield b sb' -> Yield (f a b) (sa' :!: sb' :!: Nothing)
{-# INLINE [0] zipWith #-}

zipWith3 :: (a -> b -> c -> d) -> Stream a -> Stream b -> Stream c -> Stream d
zipWith3 f (Stream nexta sa0)
           (Stream nextb sb0)
           (Stream nextc sc0) = Stream next (sa0 :!: sb0 :!: sc0 :!: Nothing)
  where
    {-# INLINE next #-}
    next (sa :!:  sb :!:  sc :!: Nothing) = case nexta sa of
      Done        -> Done
      Skip    sa' -> Skip (sa' :!: sb :!: sc :!: Nothing)
      Yield a sa' -> Skip (sa' :!: sb :!: sc :!: Just (L a :!: Nothing))

    next (sa' :!: sb :!:  sc :!: Just (L a :!: Nothing)) = case nextb sb of
      Done        -> Done
      Skip    sb' -> Skip          (sa' :!: sb' :!: sc :!: Just (L a :!: Nothing))
      Yield b sb' -> Skip          (sa' :!: sb' :!: sc :!: Just (L a :!: Just (L b)))

    next (sa' :!: sb' :!: sc :!: Just (L a :!: Just (L b))) = case nextc sc of
      Done        -> Done
      Skip    sc' -> Skip            (sa' :!: sb' :!: sc' :!: Just (L a :!: Just (L b)))
      Yield c sc' -> Yield (f a b c) (sa' :!: sb' :!: sc' :!: Nothing)
{-# INLINE [0] zipWith3 #-}

zipWith4 :: (a -> b -> c -> d -> e) -> Stream a -> Stream b -> Stream c -> Stream d -> Stream e
zipWith4 f (Stream nexta sa0)
           (Stream nextb sb0)
           (Stream nextc sc0)
           (Stream nextd sd0) = Stream next (sa0 :!: sb0 :!: sc0 :!: sd0 :!: Nothing)
  where
    {-# INLINE next #-}
    next (sa :!:  sb :!:  sc :!: sd :!: Nothing) =
        case nexta sa of
            Done        -> Done
            Skip    sa' -> Skip (sa' :!: sb :!: sc :!: sd :!: Nothing)
            Yield a sa' -> Skip (sa' :!: sb :!: sc :!: sd :!: Just (L a :!: Nothing))

    next (sa' :!: sb :!:  sc :!: sd :!: Just (L a :!: Nothing)) =
        case nextb sb of
            Done        -> Done
            Skip    sb' -> Skip (sa' :!: sb' :!: sc :!: sd :!: Just (L a :!: Nothing))
            Yield b sb' -> Skip (sa' :!: sb' :!: sc :!: sd :!: Just (L a :!: Just (L b :!: Nothing)))

    next (sa' :!: sb' :!: sc :!: sd :!: Just (L a :!: (Just (L b :!: Nothing)))) =
        case nextc sc of
            Done        -> Done
            Skip    sc' -> Skip (sa' :!: sb' :!: sc' :!: sd :!: Just (L a :!: (Just (L b :!: Nothing))))
            Yield c sc' -> Skip (sa' :!: sb' :!: sc' :!: sd :!: Just (L a :!: (Just (L b :!: Just (L c)))))

    next (sa' :!: sb' :!: sc' :!: sd :!: Just (L a :!: (Just (L b :!: Just (L c))))) =
        case nextd sd of
            Done        -> Done
            Skip    sd' -> Skip              (sa' :!: sb' :!: sc' :!: sd' :!: Just (L a :!: (Just (L b :!: Just (L c)))))
            Yield d sd' -> Yield (f a b c d) (sa' :!: sb' :!: sc' :!: sd' :!: Nothing)
{-# INLINE [0] zipWith4 #-}

unzip :: Stream (a, b) -> ([a], [b])
unzip = foldr (\(a,b) ~(as, bs) -> (a:as, b:bs)) ([], [])
{-# INLINE unzip #-}

------------------------------------------------------------------------
-- * Special streams
-- ** Functions on strings

{-
--
-- As a concatMap (snoc '\n')
--
unlines :: Stream (Stream Char) -> Stream Char
unlines (Stream next s0) = Stream next' (Right s0)
  where
    next' (Left (Stream g t, s)) = case g t of
      Done       -> Skip    (Right s)
      Skip    t' -> Skip    (Left (Stream g t', s))
      Yield x t' -> Yield x (Left (Stream g t', s))

    next' (Right s) = case next s of
      Done       -> Done
      Skip    s' -> Skip (Right s')
      Yield x s' -> Skip (Left ((snoc x '\n'), s'))
{-# INLINE [0] unlines #-}
-}

{-
--
-- As a concat . intersperse
--
unlines (Stream next s0) = Stream next' (Right s0)
  where
    -- go
    next' (Left (Stream f t, s)) = case f t of
      Done       -> Yield '\n' (Right s)
      Skip    t' -> Skip    (Left (Stream f t', s))
      Yield x t' -> Yield x (Left (Stream f t', s))

    -- to
    next' (Right s) = case next s of
      Done       -> Done
      Skip    s' -> Skip (Right s')
      Yield x s' -> Skip (Left (x, s'))
-}

{-
lines :: Stream Char -> Stream [Char]
lines (Stream next0 s0) = Stream next (Nothing :!: s0)
  where
    {-# INLINE next #-}
    next (Nothing  :!: s)     = case next0 s of
        Done           -> Done
        Skip s'        -> Skip (Nothing     :!: s')
        Yield _ _      -> Skip (Just (S []) :!: s) -- !

    next (Just (S acc) :!: s) = case next0 s of
        Done          -> Yield (reverse acc) (Nothing :!: s) -- !
        Skip s'       -> Skip (Just (S acc) :!: s')
        Yield '\n' s' -> Yield (reverse acc) (Nothing :!: s') -- reuse first state
        Yield x    s' -> Skip (Just (S (x:acc)) :!: s')

    {-# INLINE reverse #-}
    reverse :: [Char] -> [Char]
    reverse l = rev l []
      where
        rev []     a = a
        rev (x:xs) a = rev xs (x:a)
-}
{-
lines :: Stream Char -> Stream (Stream Char)
lines (Stream next s0 len) = Stream next' s0 len
  where
    next' s = case next s of
        Done    -> Done
        Skip s' -> Skip s'
-}


{-
lines' [] = []
lines' s  = let (l, s') = break (== '\n') s
            in l : case s' of
                     []      -> []
                     (_:s'') -> lines' s''
-}

{-
words :: String -> [String]
unlines :: [String] -> String
unwords :: [String] -> String
-}

------------------------------------------------------------------------
-- ** \"Set\" operations

{-
delete :: Eq a => a -> Stream a -> Stream a
difference :: Eq a => Stream a -> Stream a -> Stream a
union :: Eq a => Stream a -> Stream a -> Stream a
intersect :: Eq a => Stream a -> Stream a -> Stream a
-}

-- ** Ordered streams

{-
sort :: Ord a => Stream a -> Stream a
insert :: Ord a => a -> Stream a -> Stream a
-}

------------------------------------------------------------------------
-- * Generalized functions
-- ** The \"By\" operations
-- *** User-supplied equality (replacing an Eq context)

{-
nubBy :: (a -> a -> Bool) -> Stream a -> Stream a
deleteBy :: (a -> a -> Bool) -> a -> Stream a -> Stream a
deleteFirstsBy :: (a -> a -> Bool) -> Stream a -> Stream a -> Stream a
unionBy :: (a -> a -> Bool) -> Stream a -> Stream a -> Stream a
intersectBy :: (a -> a -> Bool) -> Stream a -> Stream a -> Stream a
groupBy :: (a -> a -> Bool) -> Stream a -> Stream (Stream a)
-}

------------------------------------------------------------------------
-- *** User-supplied comparison (replacing an Ord context)

{-
sortBy :: (a -> a -> Ordering) -> Stream a -> Stream a
-}

insertBy :: (a -> a -> Ordering) -> a -> Stream a -> Stream a
insertBy cmp x (Stream next0 s0) = Stream next (S2 :!: s0)
  where
    {-# INLINE next #-}
    -- find the insertion point
    next (S2 :!: s) = case next0 s of
        Done        -> Yield x (S1 :!: s) -- a snoc
        Skip    s'  -> Skip    (S2 :!: s')
        Yield y s' | GT == cmp x y -> Yield y (S2 :!: s')
                   | otherwise     -> Yield x (S1 :!: s)  -- insert

    -- we've inserted, now just yield the rest of the stream
    next (S1 :!: s) = case next0 s of
        Done       -> Done
        Skip    s' -> Skip    (S1 :!: s')
        Yield y s' -> Yield y (S1 :!: s')
{-# INLINE [0] insertBy #-}

maximumBy :: (a -> a -> Ordering) -> Stream a -> a
maximumBy cmp (Stream next s0) = loop0_maximumBy s0
  where
    loop0_maximumBy !s = case next s of
      Skip    s' -> expose s' $ loop0_maximumBy s'
      Yield x s' -> expose s' $ loop_maximumBy x s'
      Done       -> errorEmptyStream "maximumBy"

    loop_maximumBy z !s = case next s of
      Done       -> z
      Skip    s' -> expose s' $ loop_maximumBy z s'
      Yield x s' -> expose s' $ loop_maximumBy (max' z x) s'

    max' x y = case cmp x y of
                    GT -> x
                    _  -> y
{-# INLINE [0] maximumBy #-}

minimumBy :: (a -> a -> Ordering) -> Stream a -> a
minimumBy cmp (Stream next s0) = loop0_minimumBy s0
  where
    loop0_minimumBy !s = case next s of
      Skip    s' -> expose s' $ loop0_minimumBy s'
      Yield x s' -> expose s' $ loop_minimumBy x s'
      Done       -> errorEmptyStream "minimum"

    loop_minimumBy z !s = case next s of
      Done       -> z
      Skip    s' -> expose s' $ loop_minimumBy z s'
      Yield x s' -> expose s' $ loop_minimumBy (min' z x) s'

    min' x y = case cmp x y of
                    GT -> y
                    _  -> x
{-# INLINE [0] minimumBy #-}

------------------------------------------------------------------------
-- * The \"generic\" operations

-- length
genericLength :: Num i => Stream b -> i
genericLength (Stream next s0) = loop_genericLength s0
  where
    loop_genericLength !s = case next s of
      Done       -> 0
      Skip    s' -> expose s' $     loop_genericLength s'
      Yield _ s' -> expose s' $ 1 + loop_genericLength s'
{-# INLINE [0] genericLength #-}

--TODO: specialised generic Length for strict/atomic and associative Num
-- instances like Int and Integer

genericTake :: Integral i => i -> Stream a -> Stream a
genericTake n0 (Stream next0 s0) = Stream next (L n0 :!: s0)
  where
    {-# INLINE next #-}
    next (L 0 :!: _)  = Done
    next (L n :!: s)  = case next0 s of
        Done          -> Done
        Skip    s'    -> Skip    (L  n    :!: s')
        Yield x s'
          | n > 0     -> Yield x (L (n-1) :!: s')
          | otherwise -> error "List.genericTake: negative argument"
{-# INLINE [0] genericTake #-}

-- genericTake is defined so bizzarely!

genericDrop :: Integral i => i -> Stream a -> Stream a
genericDrop n0 (Stream next0 s0) = Stream next (Just (L n0) :!: s0)
  where
    {-# INLINE next #-}
    next (Just (L 0) :!: s) = Skip (Nothing :!: s)
    next (Just (L n) :!: s) = case next0 s of
      Done                    -> Done
      Skip    s'              -> Skip (Just (L  n)    :!: s')
      Yield _ s' | n > 0      -> Skip (Just (L (n-1)) :!: s')
                 | otherwise  -> error "List.genericDrop: negative argument"
    next (Nothing :!: s) = case next0 s of
      Done       -> Done
      Skip    s' -> Skip    (Nothing :!: s')
      Yield x s' -> Yield x (Nothing :!: s')
{-# INLINE [0] genericDrop #-}

genericIndex :: Integral a => Stream b -> a -> b
genericIndex (Stream next s0) i0 = loop_genericIndex i0 s0
  where
    loop_genericIndex i !s = case next s of
      Done                   -> error "List.genericIndex: index too large."
      Skip    s'             -> expose s' $ loop_genericIndex i     s'
      Yield x s' | i == 0    -> x
                 | i > 0     -> expose s' $ loop_genericIndex (i-1) s'
                 | otherwise -> error "List.genericIndex: negative argument."
{-# INLINE [0] genericIndex #-}

-- can we pull the n > 0 test out and do it just once?
-- probably not since we don't know what n-1 does!!
-- can only specialise it for sane Integral instances :-(


genericSplitAt :: Integral i => i -> Stream a -> ([a], [a])
genericSplitAt n0 (Stream next s0) = loop_genericSplitAt n0 s0
  where
    loop_genericSplitAt 0 !s = ([], expose s $ unstream (Stream next s))
    loop_genericSplitAt n !s = case next s of
      Done            -> ([], [])
      Skip    s'      -> expose s $ loop_genericSplitAt n s'
      Yield x s'
        | n > 0       -> (x:xs', xs'')
        | otherwise   -> error "List.genericSplitAt: negative argument"
        where
          (xs', xs'') = expose s $ loop_genericSplitAt (n-1) s'
{-# INLINE [0] genericSplitAt #-}

{-
-- No need:
genericReplicate        -- :: Integral i => i -> a -> Stream a
-}

-- ---------------------------------------------------------------------
-- Enum

{-
enumFromToNum :: (Ord a, Num a) => a -> a -> Stream a
enumFromToNum x y = Stream next (L x)
  where
    {-# INLINE next #-}
    next (L !n)
        | n > y     = Done
        | otherwise = Yield n (L (n+1))
{-# INLINE [0] enumFromToNum #-}
-}

enumFromToInt :: Int -> Int -> Stream Int
enumFromToInt x y = Stream next (L x)
  where
    {-# INLINE next #-}
    next (L !n)
        | n > y     = Done
        | otherwise = Yield n (L (n+1))
{-# INLINE [0] enumFromToInt #-}

enumDeltaInteger :: Integer -> Integer -> Stream Integer
enumDeltaInteger a d = Stream next (L a)
  where
    {-# INLINE next #-}
    next (L !x) = Yield x (L (x+d))
{-# INLINE [0] enumDeltaInteger #-}

enumFromToChar :: Char -> Char -> Stream Char
enumFromToChar x y = Stream next (L (ord x))
  where
    m = ord y

    {-# INLINE next #-}
    next (L !n)
        | n > m     = Done
        | otherwise = Yield (chr n) (L (n+1))
{-# INLINE [0] enumFromToChar #-}

-- ---------------------------------------------------------------------
-- Monadic stuff

-- Most monadic list functions can be defined in terms of foldr so don't
-- need explicit stream implementations. The one exception is foldM:
--

foldM :: Monad m => (b -> a -> m b) -> b -> Stream a -> m b
foldM f z0 (Stream next s0) = loop_foldl z0 s0
  where
    loop_foldl z !s = case next s of
      Done       -> Monad.return z
      Skip    s' -> expose s' $                  loop_foldl z  s'
      Yield x s' -> expose s' $ f z x >>= \z' -> loop_foldl z' s'
{-# INLINE [0] foldM #-}

foldM_ :: Monad m => (b -> a -> m b) -> b -> Stream a -> m ()
foldM_ f z0 (Stream next s0) = loop_foldl z0 s0
  where
    loop_foldl z !s = case next s of
      Done       -> Monad.return ()
      Skip    s' -> expose s' $                  loop_foldl z  s'
      Yield x s' -> expose s' $ f z x >>= \z' -> loop_foldl z' s'
{-# INLINE [0] foldM_ #-}


-- ---------------------------------------------------------------------
-- List comprehension desugaring

return :: a -> Stream a
return e = Stream next S1
  where
    {-# INLINE next #-}
    next S1 = Yield e S2
    next S2 = Done
{-# INLINE [0] return #-}

guard :: Bool -> Stream a -> Stream a
guard b (Stream next0 s0) = Stream next (S1 :!: s0)
  where
    {-# INLINE next #-}
    next (S1 :!: s) = if b then Skip (S2 :!: s) else Done
    next (S2 :!: s) = case next0 s of
      Done       -> Done
      Skip    s' -> Skip    (S2 :!: s')
      Yield x s' -> Yield x (S2 :!: s')
{-# INLINE [0] guard #-}

bind :: (a -> Bool) -> (a -> Stream b) -> Stream a -> Stream b
bind b f (Stream next0 s0) = Stream next (s0 :!: Nothing)
  where
    {-# INLINE next #-}
    next (s :!: Nothing) = case next0 s of
      Done          -> Done
      Skip    s'    -> Skip    (s' :!: Nothing)
      Yield x s'
        | b x       -> Skip (s' :!: Just (f x))
        | otherwise -> Skip (s' :!: Nothing)

    next (s :!: Just (Stream next1 s1)) = case next1 s1 of
      Done        -> Skip    (s :!: Nothing)
      Skip    s1' -> Skip    (s :!: Just (Stream next1 s1'))
      Yield x s1' -> Yield x (s :!: Just (Stream next1 s1'))
{-# INLINE [0] bind #-}

mapFilter :: (a -> Bool) -> (a -> b) -> Stream a -> Stream b
mapFilter b f (Stream next0 s0) = Stream next s0
  where
    {-# INLINE next #-}
    next s = case next0 s of
      Done          -> Done
      Skip    s'    -> Skip        s'
      Yield x s'
        | b x       -> Yield (f x) s'
        | otherwise -> Skip        s'
{-# INLINE [0] mapFilter #-}

declare :: (a -> Stream b) -> a -> Stream b
declare f bs = Stream next (f bs)
  where
    {-# INLINE next #-}
    next (Stream next0 s) = case next0 s of
      Done       -> Done
      Skip    s' -> Skip    (Stream next0 s')
      Yield x s' -> Yield x (Stream next0 s')
{-# INLINE [0] declare #-}
-}
