{-# OPTIONS --safe #-}
module Meta.Effect where

open import Meta.Effect.Alt         public
open import Meta.Effect.Alternative public
open import Meta.Effect.Base        public
open import Meta.Effect.Choice      public
open import Meta.Effect.Container   public
open import Meta.Effect.Bind        public
open import Meta.Effect.Foldable    public
open import Meta.Effect.Idiom       public
open import Meta.Effect.Map         public
open import Meta.Effect.Monoidal    public
open import Meta.Effect.Traversable public

open Choice ⦃ ... ⦄ public
{-# DISPLAY Choice._<|>_ _ m = _<|>_ m #-}
open Alt ⦃ ... ⦄ public
{-# DISPLAY Alt.fail _ = fail #-}
open Alternative ⦃ ... ⦄ public
{-# DISPLAY Alternative.empty _ = empty #-}
{-# DISPLAY Alternative._<+>_ _ m = _<+>_ m #-}
open Monoidal ⦃ ... ⦄ public
{-# DISPLAY Monoidal.unit _ = unit #-}
{-# DISPLAY Monoidal._<,>_ _ m = _<,>_ m #-}

open Map ⦃ ... ⦄ public
{-# DISPLAY Map.map _ f = map f #-}
open Lawful-Map ⦃ ... ⦄ public
open Idiom ⦃ ... ⦄ public
{-# DISPLAY Idiom.pure _ x = pure x #-}
{-# DISPLAY Idiom._<*>_ _ m = _<*>_ m #-}
open Lawful-Idiom ⦃ ... ⦄ public
open Bind ⦃ ... ⦄ public
{-# DISPLAY Bind._>>=_ _ m = _>>=_ m #-}
open Lawful-Bind ⦃ ... ⦄ public

open Foldable ⦃ ... ⦄ public
{-# DISPLAY Foldable.fold-r _ f = fold-r f #-}
open Traversable ⦃ ... ⦄ public
{-# DISPLAY Traversable.traverse _ f = traverse f #-}
