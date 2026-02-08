-- Based on initial code provided by Stefan Sabev
module Language.Carneades.Cyclic(cyclic) where
import Data.Graph.Inductive

cyclic :: (DynGraph g) => g a b -> Bool
cyclic g | not (null leafs) = cyclic (delNodes leafs g)
         | otherwise        = not (isEmpty g)
  where leafs = filter (isLeaf g) (nodes g)

isLeaf :: (DynGraph g) => g a b -> Node -> Bool
isLeaf g n = n `notElem` map fst (edges g)