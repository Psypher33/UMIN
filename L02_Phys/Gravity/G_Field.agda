{-# OPTIONS --cubical --guardedness #-}

module UMIN.L02_Phys.Gravity.G_Field where

open import Cubical.Foundations.Prelude
open import Agda.Builtin.Float

-- 1. ファイルをインポート（トップレベルの LN2-Value が自動的に見えます）
open import UMIN.L03_Func.NumericalExperiment.PauliStates

private
  _+f_ = primFloatPlus
  _*f_ = primFloatTimes

-- =========================================================================
-- [L02_Phys] 重力作用のドレスアップ
-- =========================================================================

record GFieldConfiguration : Type where
  constructor g-config
  field
    coupling-strength : Float 
    dark-energy-bias  : Float

-- 2. 修正：トップレベルに公開された値 (LN2-Value) を直接使用
-- これにより、モジュール階層の問題やインデントエラーを完全に回避します
entropic-gravity-action : GFieldConfiguration → Float
entropic-gravity-action c = 
  (GFieldConfiguration.coupling-strength c *f LN2-Value) 
  +f (GFieldConfiguration.dark-energy-bias c)