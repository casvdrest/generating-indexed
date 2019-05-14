fbind :: (r -> a) -> (a -> r -> b) -> r -> b
fbind  = undefined

type State s a = s -> (a, s)

sbind :: State s a -> (a -> State s b) -> State s b
sbind = flip ((.) . uncurry)