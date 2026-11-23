module

public import Mathlib

@[expose] public section

namespace Formalism.SL.IwahoriBlocks

variable {E : Type*} [CommRing E] [StarRing E] {V : Type*} [AddCommGroup V] [Module E V]

def IsHerm (h : V →ₗ[E] V →ₗ⋆[E] E) : Prop := ∀ v w, h w v = star (h v w)

def eich (h : V →ₗ[E] V →ₗ⋆[E] E) (x u : V) (s : E) (v : V) : V :=
  v + h v u • x - h v x • (u + s • x)

end Formalism.SL.IwahoriBlocks
