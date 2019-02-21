module BackEnd.MakeGraph where

import Data.HashMap as HashMap hiding (map)
import Algebra.Graph.AdjacencyMap as AdjGraph
import BackEnd.FlowGraph
import BackEnd.Assem as Assem


-- transform instructions to control flow graph
-- node in control flow graph are int, which maps to an instruction
-- transformation do two main thing:
-- 1. add edge from instruction to instruction (node to node, int to int)
-- 2. add mapping : node -> temps defined at the node (def)
-- 3. add mapping : node -> temps used at the node    (use)
instrsToGraph :: [Assem.Instr] -> FlowGraph
instrsToGraph instrs = fGraph { nodes = map fst indexed,
                                assems = HashMap.fromList indexed }
  where indexed = zip [1..] instrs -- index instructions

        -- create a mapping from label to node (int)
        labelTable =
          foldl (\acc (i, instr) ->
                   case instr of
                     ILABEL _ lab -> insert lab i acc
                     otherwise -> acc ) HashMap.empty indexed
          
        fGraph = instrsToGraph' indexed newFlowGraph

        instrsToGraph' :: [(Int, Assem.Instr)] -> FlowGraph -> FlowGraph
        instrsToGraph' [] fGraph = fGraph

        instrsToGraph' (curr@(index, instr@(IOPER _ dst src _)):rest) fGraph =
          instrsToGraph' rest $ fGraph { control = adjGraph', def = def', use = use' }
          where
            targets = map (\l -> labelTable ! l) (jump instr)

            -- add edge from current node to jump targets
            adjGraph' =
              foldl (\acc t -> overlay (edge index t) acc) (control fGraph) targets
              
            -- add def and use temps
            def' = insertWith (++) index dst (def fGraph)
            use' = insertWith (++) index src (use fGraph)

        instrsToGraph' (curr@(index, ILABEL _ _):rest) fGraph =
          instrsToGraph' rest $ fGraph { control = adjGraph'}
          where adjGraph' = overlay (edge index (index+1)) (control fGraph)
          -- add edge from current node to next instruction

        instrsToGraph' ((index, (IMOV _ (dst:_) (src:_))):rest) fGraph =
          instrsToGraph' rest $ fGraph { control = adjGraph',
                                         def = insertWith (++) index [dst] (def fGraph),
                                         use = insertWith (++) index [src] (use fGraph) }
          where -- add edge from current node to next instruction
                adjGraph' = overlay (edge index (index+1)) (control fGraph)
