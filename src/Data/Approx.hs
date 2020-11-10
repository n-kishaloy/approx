{-|
Module      : Approx
Description : Implement Approx for Double, Floats and structures
Copyright   : (c) 2020 Kishaloy Neogi
License     : MIT
Maintainer  : Kishaloy Neogi
Email       : nkishaloy@yahoo.com

The library is created to allow for a easy-to-use reasonable way of emulating approx in Haskell. The codes are all in /pure/ Haskell. The idea is to have a natural mathematical feel in writing code, with operators which just works when working with Double and Float and their composite types like lists, vectors etc. 

The __Approx__ module defines 2 operators __@=~@__ and __@/~@__, which are for checking /nearly equal to/ and /not nearly equal to/ respectively. 

Both the operators __=~__ and __/~__ are put under the class __Approx__. 

At least one of the operators have to be defined and the other gets automatically defined. 

The library already defines the functions for some of the basic / common types. 

For types where __Eq__ is defined like __Char, Bool, Int, Day, Text__ the approx is simply replaced with __==__. 

For __Float__ and __Double__, the following formula is used, 

@
if max ( |x|, |y| ) < epsilon_Zero
then True
else 
  if |x - y| / max ( |x|, |y| ) < epsilon_Eq
  then True
  else False
@

The motivation for defining Approx for classes for which Eq is also defined is to allow for composite types where both Eq and Approx would be present. For example, the following code evaluates to __@True@__, even though the tuple is of type @(Int,Double,Text,[Int],[[Char]],[Double])@.

@
((2,5.35,"happ",[1,2],["ret","we"],[6.78,3.5]) 
    :: (Int,Double,Text,[Int],[[Char]],[Double])) 
    
    =~ (2,5.35,"happ",[1,2],["ret","we"],[6.78,3.5])
@

For UTCTime, the approx operator checks for equality to the nearest minute. The following expression evaluates to __@True@__.

@
(parseTimeM True defaultTimeLocale "%Y-%m-%d %H:%M:%S" "2020-01-15 15:02:15" 
    :: Maybe UTCTime) 

    =~ parseTimeM True defaultTimeLocale "%Y-%m-%d %H:%M:%S" "2020-01-15 15:01:50"
@

The library also provides approx for Complex and common structures like __List, Boxed and Unboxed Vector, Hashmap, Tuples__ and __Maybe__. For all lists, tuples, hashmaps and vectors, the approximation is checked right down to the elements and the order for lists and vectors are important. 

For lists, only finite lists are supported. Any use of infinite lists would cause a runtime error.

You may see the github repository at <https://github.com/n-kishaloy/approx>

-}


{-# LANGUAGE Strict #-}

module Data.Approx
( 
-- *How to use this library
-- |Add @approx@ to build-depends and @import Data.Approx@

-- *Documentation
  Approx (..)

) where

import Data.List (foldl')
-- import Data.Vector.Unboxed ((!),(//))
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as M
import qualified Data.Vector as V
import Data.Time (Day, UTCTime)
import Data.Time.Clock (diffUTCTime)
import qualified Data.HashMap.Strict as Hm
import Data.Hashable

import Data.Text (Text)
import qualified Data.Complex as Cx
import Data.Complex (Complex ( (:+) ) )

epsZeroDouble :: Double
epsZeroDouble = 1e-8;   {-# INLINE epsZeroDouble  #-}

epsEqDouble :: Double
epsEqDouble   = 1e-7;   {-# INLINE epsEqDouble    #-}

epsZeroFloat :: Float
epsZeroFloat = 1e-6;    {-# INLINE epsZeroFloat   #-}

epsEqFloat :: Float
epsEqFloat   = 1e-5;    {-# INLINE epsEqFloat     #-}

infix 4 =~, /~

-- |The class @Approx@ defines 2 operators __@=~@__ and __@/~@__, which are for checking /nearly equal to/ and /not nearly equal to/ respectively.
class Approx a where 
  (=~), (/~) :: a -> a -> Bool 
   
  (=~) x y = not (x /~ y)
  {-# INLINE (=~) #-}
  (/~) x y = not (x =~ y)
  {-# INLINE (/~) #-}

  {-# MINIMAL (=~) | (/~) #-}

instance Approx Day where x =~ y = x == y; {-# INLINE (=~) #-}

instance Approx Char where x =~ y = x == y; {-# INLINE (=~) #-}

instance Approx Bool where x =~ y = x == y; {-# INLINE (=~) #-}

instance Approx Text where x =~ y = x == y; {-# INLINE (=~) #-}

instance Approx Int where x =~ y = x == y; {-# INLINE (=~) #-}

instance Approx Integer where x =~ y = x == y; {-# INLINE (=~) #-}


instance Approx UTCTime where 
  x =~ y = (round . (/60.0) . realToFrac $ x `diffUTCTime` y) == 0
  {-# INLINE (=~) #-}

instance Approx a => Approx (Cx.Complex a) where
  (a :+ b) =~ (x :+ y) = (a =~ x) && (b =~ y); {-# INLINE (=~) #-}

instance Approx Float where
  x =~ y = if (mx < epsZeroFloat) || (abs (x-y)) / mx < epsEqFloat then True else False 
    where mx = (max (abs x) (abs y))
  {-# INLINE (=~) #-}

instance Approx Double where
  x =~ y = if (mx < epsZeroDouble) || (abs (x-y)) / mx < epsEqDouble then True else False 
    where mx = (max (abs x) (abs y))
  {-# INLINE (=~) #-}

instance Approx a => Approx (Maybe a) where
  Nothing =~ Nothing  =   True
  Just x  =~ Just y   =   x =~ y 
  _       =~ _        =   False
  {-# INLINE (=~) #-}

instance Approx a => Approx [a] where 
  x =~ y = (length x == length y) && (foldr (&&) True $ zipWith (=~) x y)

instance (Approx a, Approx b) => Approx (a, b) where
  (x,y) =~ (a,b) = 
    (   (x =~ a) 
    &&  (y =~ b)
    )
  {-# INLINE (=~) #-}

instance (Approx a, Approx b, Approx c) => Approx (a, b, c) where
  (x,y,z) =~ (a,b,c) = 
    (   (x =~ a) 
    &&  (y =~ b) 
    &&  (z =~ c)
    )
  {-# INLINE (=~) #-}

instance (Approx a,Approx b,Approx c,Approx d) => Approx (a,b,c,d) where
  (x,y,z,u) =~ (a,b,c,d) = 
    (   (x =~ a) 
    &&  (y =~ b) 
    &&  (z =~ c) 
    &&  (u =~ d)
    )
  {-# INLINE (=~) #-}

instance (Approx a,Approx b,Approx c,Approx d, Approx e) => Approx (a,b,c,d,e) where
  (x,y,z,u,v) =~ (a,b,c,d,e) = 
    (   (x =~ a) 
    &&  (y =~ b) 
    &&  (z =~ c) 
    &&  (u =~ d) 
    &&  (v =~ e)
    )
  {-# INLINE (=~) #-}

instance (Approx a,Approx b,Approx c,Approx d, Approx e, Approx f) => Approx (a,b,c,d,e,f) where
  (x,y,z,u,v,w) =~ (a,b,c,d,e,f) = 
    (   (x =~ a) 
    &&  (y =~ b) 
    &&  (z =~ c) 
    &&  (u =~ d) 
    &&  (v =~ e) 
    &&  (w =~ f)
    )
  {-# INLINE (=~) #-}

instance (Approx a,Approx b,Approx c,Approx d, Approx e, Approx f, Approx g) => Approx (a,b,c,d,e,f,g) where
  (x,y,z,u,v,w,p) =~ (a,b,c,d,e,f,g) = 
    (   (x =~ a) 
    &&  (y =~ b) 
    &&  (z =~ c) 
    &&  (u =~ d) 
    &&  (v =~ e) 
    &&  (w =~ f) 
    &&  (p =~ g)
    )
  {-# INLINE (=~) #-}

instance (Approx a,Approx b,Approx c,Approx d, Approx e, Approx f, Approx g, Approx h) => Approx (a,b,c,d,e,f,g,h) where
  (x,y,z,u,v,w,p,q) =~ (a,b,c,d,e,f,g,h) = 
    (   (x =~ a) 
    &&  (y =~ b) 
    &&  (z =~ c) 
    &&  (u =~ d) 
    &&  (v =~ e) 
    &&  (w =~ f) 
    &&  (p =~ g) 
    &&  (q =~ h)
    )
  {-# INLINE (=~) #-}

instance (Approx a,Approx b,Approx c,Approx d, Approx e, Approx f, Approx g, Approx h, Approx i) => Approx (a,b,c,d,e,f,g,h,i) where
  (x,y,z,u,v,w,p,q,r) =~ (a,b,c,d,e,f,g,h,i) = 
    (   (x =~ a) 
    &&  (y =~ b) 
    &&  (z =~ c) 
    &&  (u =~ d) 
    &&  (v =~ e) 
    &&  (w =~ f) 
    &&  (p =~ g) 
    &&  (q =~ h) 
    &&  (r =~ i)
    )
  {-# INLINE (=~) #-}

instance (Approx a,Approx b,Approx c,Approx d, Approx e, Approx f, Approx g, Approx h, Approx i, Approx j) => Approx (a,b,c,d,e,f,g,h,i,j) where
  (x,y,z,u,v,w,p,q,r,s) =~ (a,b,c,d,e,f,g,h,i,j) = 
    (   (x =~ a) 
    &&  (y =~ b) 
    &&  (z =~ c) 
    &&  (u =~ d) 
    &&  (v =~ e) 
    &&  (w =~ f) 
    &&  (p =~ g) 
    &&  (q =~ h) 
    &&  (r =~ i) 
    &&  (s =~ j)
    )
  {-# INLINE (=~) #-}

instance (Approx a,Approx b,Approx c,Approx d, Approx e, Approx f, Approx g, Approx h, Approx i, Approx j, Approx k) => Approx (a,b,c,d,e,f,g,h,i,j,k) where
  (x,y,z,u,v,w,p,q,r,s,t) =~ (a,b,c,d,e,f,g,h,i,j,k) = 
    (   (x =~ a) 
    &&  (y =~ b) 
    &&  (z =~ c) 
    &&  (u =~ d) 
    &&  (v =~ e) 
    &&  (w =~ f) 
    &&  (p =~ g) 
    &&  (q =~ h) 
    &&  (r =~ i) 
    &&  (s =~ j) 
    &&  (t =~ k)
    )
  {-# INLINE (=~) #-}

instance (M.Unbox a, Approx a) => Approx (U.Vector a) where 
  x =~ y = (U.length x==U.length y) && (U.foldr (&&) True $ U.zipWith (=~) x y)

instance (Approx a) => Approx (V.Vector a) where 
  x =~ y = (V.length x==V.length y) && (V.foldr (&&) True $ V.zipWith (=~) x y)

instance (Eq a, Hashable a, Approx b) => Approx (Hm.HashMap a b) where
  x =~ y = (fz x y) && (fz y x) where
    fz p q = foldl' (f p) True $ Hm.toList q
    f p t z = t && ((Hm.lookup k p) =~ (Just v)) where (k,v) = z 
