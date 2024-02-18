
module Names where

open import Foundations.Base
open import Data.String
open import Data.List

record TyNameₛ    : 𝒰 where constructor Ty;    field name : String
record CtorNameₛ  : 𝒰 where constructor Ctor;  field name : String
record FieldNameₛ : 𝒰 where constructor Field; field name : String
record ExprNameₛ  : 𝒰 where constructor Expr;  field name : String
open TyNameₛ   public
open CtorNameₛ public
open FieldNameₛ public
open ExprNameₛ public

𝕋 = List TyNameₛ
𝔼 = List ExprNameₛ

variable
  t : TyNameₛ
  e : ExprNameₛ
