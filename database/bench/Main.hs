{-# LANGUAGE OverloadedStrings #-}
module Main where

import ExtractionExamples
import Interpreter

main :: IO ()
main = do
  h <- interpret ex1_setup
  interpret (ex1_write1 h 1 "value")
  interpret (ex2_par_reads h 1 10000000)
  interpret (ex2_seq_reads h 1 10000000)
  return ()
