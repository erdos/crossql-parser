#!/usr/bin/env runhaskell

{-# OPTIONS_GHC -Wall -Werror -fwarn-incomplete-uni-patterns  #-}
{-# LANGUAGE OverloadedStrings #-}

import SQLParser (parse)
import Util (pr)
import TextbookRelAlg (pipeline)
import Text.Parsec (runParser)

import Network.Wai
import Network.HTTP.Types
import Network.Wai.Handler.Warp (run)

import qualified Data.ByteString.Lazy.Char8 as LC
import qualified Data.ByteString as BS
import Data.Char (chr)

handleLine :: String -> Either String String
handleLine line =
  case runParser parse () "" line of
    (Left pe) -> Left $ pr pe
    (Right b) -> Right $ either pr pr (pipeline b)

responseJson :: Bool -> String -> Response
responseJson s x = responseLBS (if s then status200 else status400) [("Content-Type", "text/plain")] $ LC.pack x

app :: Application
app request respond = do
  body <- requestBody request -- byte string
  respond $ case (handleLine (map (chr . fromEnum) (BS.unpack body))) of
    Left err -> responseJson False err
    Right ok -> responseJson True ok

main :: IO ()
main = run 8080 app
