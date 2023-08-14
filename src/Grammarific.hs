{-# language TypeFamilies #-}

module Grammarific
  ( Grammar(..)
  , Parser(..)
  , Rule(..)
    -- * Evaluation
  , evaluateInitial
    -- * Build
  , define
  , rule
  , token
  ) where

import Data.Kind
import Data.Type.Equality

newtype Grammar r t = Grammar [Rule r t]

define :: r a -> [Parser r t a] -> Rule r t
define = RuleCon

rule :: r a -> Parser r t a
rule = Rule

token :: t a -> Parser r t a
token = Match

-- Rule is comprised of alternatives.
data Rule :: (Type -> Type) -> (Type -> Type) -> Type where
  RuleCon ::
       r x -- identifier
    -> [Parser r t x] -- alternatives
    -> Rule r t

-- | Functor and Applicative instance for Parser are law abiding up to
-- observation. 
data Parser :: (Type -> Type) -> (Type -> Type) -> Type -> Type where
  Pure :: a -> Parser r t a
  Apply :: Parser r t (a -> b) -> Parser r t a -> Parser r t b
  Match :: t a -> Parser r t a
  Rule :: r a -> Parser r t a

instance Functor (Parser r t) where
  fmap f p = Apply (Pure f) p

instance Applicative (Parser r t) where
  pure = Pure
  (<*>) = Apply

class Matcher (t :: Type -> Type) where
  type Match t :: Type
  match :: t x -> Match t -> Maybe x

evaluateInitial :: (TestEquality r, Matcher t)
  => Grammar r t
  -> r a
  -> [Match t]
  -> Maybe (a, [Match t])
evaluateInitial g ruleId input = do
  p <- lookupRule g ruleId
  evaluateAlts g p input

lookupRule :: TestEquality r => Grammar r t -> r a -> Maybe [Parser r t a]
lookupRule (Grammar []) _ = Nothing
lookupRule (Grammar (RuleCon ruleId ruleBody : xs)) needle =
  case testEquality needle ruleId of
    Nothing -> lookupRule (Grammar xs) needle
    Just Refl -> Just ruleBody

evaluateAlts :: (TestEquality r, Matcher t)
  => Grammar r t
  -> [Parser r t a]
  -> [Match t]
  -> Maybe (a,[Match t])
evaluateAlts _ [] _ = Nothing
evaluateAlts g (p : ps) ts = case evaluateParser g p ts of
  Nothing -> evaluateAlts g ps ts
  Just (a,ts') -> Just (a,ts')

evaluateParser :: (TestEquality r, Matcher t)
  => Grammar r t
  -> Parser r t a
  -> [Match t]
  -> Maybe (a,[Match t])
evaluateParser g p xs = case p of
  Rule ruleId -> do
    p' <- lookupRule g ruleId
    evaluateAlts g p' xs
  Pure a -> Just (a,xs)
  Match expectation -> case xs of
    [] -> Nothing
    y : ys -> case match expectation y of
      Just a -> Just (a,ys)
      Nothing -> Nothing
  Apply f x -> do
    (f',xs') <- evaluateParser g f xs
    (x',xs'') <- evaluateParser g x xs'
    pure (f' x',xs'')
