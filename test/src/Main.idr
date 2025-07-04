module Main

import Hedgehog
import Map
import RRBVector
import RRBVector1
import Seq.Unsized
import Set

%default total

main : IO ()
main = test
  [ Map.props
  , RRBVector.props
  , RRBVector1.props
  , Seq.Unsized.props
  , Set.props
  ]
