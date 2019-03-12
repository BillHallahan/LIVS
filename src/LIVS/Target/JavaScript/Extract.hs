-- Hides the warnings about deriving 
{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}

module LIVS.Target.JavaScript.Extract where

import LIVS.Language.AST

import Language.JavaScript.Parser
import Language.JavaScript.Parser.AST

$(derivingASTWithContainers ''JSExpression)