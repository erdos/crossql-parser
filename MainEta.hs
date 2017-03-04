{-# LANGUAGE MagicHash #-}

module MainEta (handler, main) where

import Java
import Main (handleLine)

data {-# CLASS "erdos.socql.Action" #-} Action = Action (Object# Action)

handler :: String -> Java Action String
handler s = return $ handleLine s

foreign export java handler :: Java Action String

main :: IO ()
main = return ()
