#!/usr/bin/env runhaskell

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

module Part1.Chapter02_TypesAndFunctions where

import Control.Concurrent (threadDelay)
import Control.Monad.State
import System.Random (randomIO)

main :: IO ()
main = do
  flip evalStateT newCache $ do
    liftIO $ putStrLn "Delay:"
    write =<< delayedTimes2 2
    write =<< delayedTimes2 4
    write =<< delayedTimes2 2
    write =<< delayedTimes2 4
    liftIO $ putStrLn ""
  flip evalStateT newCache $ do
    liftIO $ putStrLn "Randomness:"
    write =<< random ()
    write =<< random ()
    write =<< memoizedRandom ()
    write =<< memoizedRandom ()

write :: (MonadIO m, Show a) => a -> m ()
write = liftIO . putStrLn . show

delayedTimes2 :: Int -> StateT (MemoizationCache Int Int) IO Int
delayedTimes2 = memoize $ \ x -> do
  liftIO $ threadDelay 1000000
  return $ x * 2

random :: () -> StateT (MemoizationCache () Int) IO Int
random () = liftIO randomIO

memoizedRandom :: () -> StateT (MemoizationCache () Int) IO Int
memoizedRandom = memoize random

data MemoizationCache a b = Eq a => MemoizationCache [(a, b)]

newCache :: Eq a => MemoizationCache a b
newCache = MemoizationCache []

memoize :: MonadState (MemoizationCache a b) m => (a -> m b) -> a -> m b
memoize f key = do
  MemoizationCache cache <- get
  case lookup key cache of
    Just value -> return value
    Nothing -> do
      value <- f key
      put $ MemoizationCache ((key, value) : cache)
      return value
