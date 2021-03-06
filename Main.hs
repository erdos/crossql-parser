#!/usr/bin/env runhaskell

{-# OPTIONS_GHC -Wall -Werror -fwarn-incomplete-uni-patterns  #-}

module Main (main, handleLine) where

import SQLParser (parse)
-- import SQLStrategy (transformer)
import Util (pr)
import TextbookRelAlg (pipeline)

import Control.Monad
import Text.Parsec (runParser)
import System.IO (hSetBuffering, stdout, BufferMode(LineBuffering))

handleLine :: String -> String
handleLine line =
  case runParser parse () "" line of
    (Left pe) -> pr pe
    (Right b) -> either pr pr (pipeline b)

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering;
  c <- getContents;
  forM_ (lines c) (putStrLn . handleLine)
