module Trees where

{-- 

Our objects are n-dimensional cubes represented as complete binary trees of
different heights. 

--}

-- plain types: the names are for testing
data T = Zero | One | Plus T T | Times T T | Name String
  deriving Show

data NCube = Leaf T 
           | Node NCube NCube -- left is plus; right is minus
  deriving Show

-- examples

-- zeroth level types

t1 = Leaf (Plus One One)
t2 = Leaf One
t3 = Leaf (Times One (Plus One One))
t4 = Leaf (Plus One (Plus One One))

-- first level types (a-b)

tt1 = Node t1 t2
tt2 = Node t3 t4

-- second level types ((a-b)-(c-d))

ttt1 = Node tt1 tt2

-- multiplication

times :: NCube -> NCube -> NCube
times (Leaf t1) (Leaf t2) = Leaf (Times t1 t2)
times (Leaf t) (Node o1 o2) = Node (times (Leaf t) o1) (times (Leaf t) o2)
times (Node o1 o2) o = Node (times o1 o) (times o2 o)

test1 = times 
          (Node (Leaf (Name "x+")) (Leaf (Name "y-")))
          (Node (Node (Leaf (Name "a+")) (Leaf (Name "b-")))
                (Node (Leaf (Name "c-")) (Leaf (Name "d+"))))

{--
Node (Node 
       (Node (Leaf (Times (Name "x+") (Name "a+"))) 
             (Leaf (Times (Name "x+") (Name "b-")))) 
       (Node (Leaf (Times (Name "x+") (Name "c-"))) 
             (Leaf (Times (Name "x+") (Name "d+"))))) 
     (Node 
       (Node (Leaf (Times (Name "y-") (Name "a+"))) 
             (Leaf (Times (Name "y-") (Name "b-")))) 
       (Node (Leaf (Times (Name "y-") (Name "c-"))) 
             (Leaf (Times (Name "y-") (Name "d+")))))
--}

-- addition (extend the shorter tree) 

add :: NCube -> NCube -> NCube
add (Leaf t1) (Leaf t2) = Leaf (Plus t1 t2)
add (Leaf t) (Node o1 o2) = add (Node (Leaf t) (Leaf Zero)) (Node o1 o2)
add (Node o1 o2) (Leaf t) = add (Node o1 o2) (Node (Leaf t) (Leaf Zero))
add (Node o1 o2) (Node o3 o4) = Node (add o1 o3) (add o2 o4)

test2 = add
          (Node (Leaf (Name "x+")) (Leaf (Name "y-")))
          (Node (Node (Leaf (Name "a+")) (Leaf (Name "b-")))
                (Node (Leaf (Name "c-")) (Leaf (Name "d+"))))

{--

Node (Node (Leaf (Plus (Name "x+") (Name "a+"))) 
           (Leaf (Plus Zero (Name "b-")))) 
     (Node (Leaf (Plus (Name "y-") (Name "c-"))) 
           (Leaf (Plus Zero (Name "d+"))))

--}

-- What are the morphisms between these cubes? 

{--

mor :: NCube -> NCube -> NMorphism
mor (Leaf t1) (Leaf t2) = Base (t1 :<=> t2) 
mor (Node o1 o2) (Node o3 o4) = mor (Either o1 o4) (Either o3 o2)

--}