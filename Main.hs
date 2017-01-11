#!/usr/bin/env runhaskell

{-# LANGUAGE FlexibleContexts#-}
{-# OPTIONS_GHC -Wall -Werror #-}

module Main (main) where

import SQLParser (parse)
import SQLStrategy (transformer)
import Util (pr)

import Control.Monad
import Text.Parsec (runParser)
import System.IO (hSetBuffering, stdout, BufferMode(LineBuffering))

handleLine :: String -> String
handleLine line =
  case runParser parse () "" line of
    (Left pe) -> pr pe
    (Right b) -> pr $ transformer b

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering;
  c <- getContents;
  forM_ (lines c) (putStrLn . handleLine)
