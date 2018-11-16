{-# OPTIONS_GHC -fno-warn-orphans #-}
module Utils.MonadInstance where

import Proc
import Unsafe.Coerce

instance Functor (Coq_proc op) where
  fmap f p = Bind (unsafeCoerce p) (Ret . f . unsafeCoerce)

instance Applicative (Coq_proc op) where
  pure = Ret
  af <*> x = Bind (unsafeCoerce af) (\f -> unsafeCoerce f x)

instance Monad (Coq_proc op) where
  x >>= f = Bind (unsafeCoerce x) (f . unsafeCoerce)
