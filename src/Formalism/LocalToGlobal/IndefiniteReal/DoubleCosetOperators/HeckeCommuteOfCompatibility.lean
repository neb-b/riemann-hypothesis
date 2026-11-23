module

public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.UG

namespace Formalism.IndefR.NX

section Op

variable {G H : Type} [Group G] [Group H] {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W]

def RightInv (S : Set G) (φ : G → W) : Prop := ∀ g, ∀ s ∈ S, φ (g * s) = φ g

end Op

section Twist

variable {H : Type} [Group H] {k : Type} [CommRing k]

def twist (χ : H →* k) (f : H → k) : H → k := fun x => χ x * f x

theorem twist_mem {KH : Subgroup H} {χ : H →* k} (hχ : ∀ κ ∈ KH, χ κ = 1) {f : H → k} (hf : f ∈ Hecke k KH) :
    twist χ f ∈ Hecke k KH := by
  obtain ⟨hb, S, hS⟩ := hf
  refine ⟨fun a b g => ?_, S, fun g hg => hS g fun h0 => hg ?_⟩
  · simp only [twist, map_mul, hχ a a.2, hχ b b.2, one_mul, mul_one, hb a b g]
  · simp [twist, h0]

end Twist

section GLv

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ)

abbrev Kv : Subgroup (GL (Fin n) (v.adicCompletion F)) := GLint (Fin n) (Ov F v)

variable {v n} {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module ℂ W]

theorem hkN_fun_mem {χ : GL (Fin n) (v.adicCompletion F) →* ℂ} (hχ : ∀ κ ∈ Kv v n, χ κ = 1)
    {ϖ : v.adicCompletion F} (hϖ : ϖ ≠ 0) (k : ℕ) : twist χ (Tj ℂ n (Ov F v) ϖ k) ∈ Hecke ℂ (Kv v n) :=
  twist_mem hχ (Formalism.UG.Final.TjMem _ (Ov F v) ϖ ℂ n k hϖ)

end GLv

section Reps

variable {G H : Type} [Group G] [Group H] {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W]

end Reps

section Concrete

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def compV (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : GA D V) :
    GL (Fin V.rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) :=
  Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) (Formalism.IndefR.Lev.finE V h)

structure SplitEmb (V : HSp D) (K : Set (GA D V)) where
  Sp : Set (HeightOneSpectrum (𝓞 D.host.F))
  sp : ∀ v ∈ Sp, D.host.E ⊗[D.host.F] v.adicCompletion D.host.F ≃+* v.adicCompletion D.host.F × v.adicCompletion D.host.F
  sp_sig : ∀ v (hv : v ∈ Sp) x, sp v hv (sigR D.sp.cm.sig (v.adicCompletion D.host.F) x) = swapR _ (sp v hv x)
  sp_alg : ∀ v (hv : v ∈ Sp) (a : v.adicCompletion D.host.F), sp v hv ((1 : D.host.E) ⊗ₜ[D.host.F] a) = (a, a)
  emb : ∀ v : HeightOneSpectrum (𝓞 D.host.F), GL (Fin V.rank) (v.adicCompletion D.host.F) →* GA D V
  emb_fin : ∀ v a, emb v a ∈ GfC V
  emb_at : ∀ v (hv : v ∈ Sp) a, Formalism.UG.bc ((RingHom.fst _ _).comp (sp v hv).toRingHom) (compV V v (emb v a)) = a
  emb_off : ∀ v ∈ Sp, ∀ a, ∀ w, w ≠ v → compV V w (emb v a) = 1
  emb_K : ∀ v, ∀ a ∈ Kv v V.rank, emb v a ∈ K
  emb_comm : ∀ v v', v ≠ v' → ∀ a b, emb v a * emb v' b = emb v' b * emb v a

variable {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

end Concrete

section Checks

open Formalism.BasicNotions Formalism.L2.Theta

end Checks

end Formalism.IndefR.NX
