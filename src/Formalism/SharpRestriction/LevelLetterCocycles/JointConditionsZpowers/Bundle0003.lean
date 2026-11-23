module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ArchimedeanSignatureMatchingOfJointCond
section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

open NumberField IsDedekindDomain

section Roots

variable {g : ℕ} [Fact g.Prime]

theorem rootsBar_mul (a b : (ZMod g)[X]) (ha : a ≠ 0) (hb : b ≠ 0) :
    Formalism.CyclotomicNorms.rootsBar (a * b) = Formalism.CyclotomicNorms.rootsBar a + Formalism.CyclotomicNorms.rootsBar b := by
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [Polynomial.map_mul, Polynomial.roots_mul]
  have hi : Function.Injective (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) := (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective
  exact mul_ne_zero ((Polynomial.map_ne_zero_iff hi).2 ha) ((Polynomial.map_ne_zero_iff hi).2 hb)

theorem rootsBar_pow (a : (ZMod g)[X]) (d : ℕ) : Formalism.CyclotomicNorms.rootsBar (a ^ d) = d • Formalism.CyclotomicNorms.rootsBar a := by
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [Polynomial.map_pow, Polynomial.roots_pow]

theorem card_rootsBar (a : (ZMod g)[X]) : Multiset.card (Formalism.CyclotomicNorms.rootsBar a) = a.natDegree := by
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits (a.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)))),
    Polynomial.natDegree_map]

theorem rootsBar_frob (a : (ZMod g)[X]) :
    (Formalism.CyclotomicNorms.rootsBar a).map (fun x => x ^ g) = Formalism.CyclotomicNorms.rootsBar a := by
  unfold Formalism.CyclotomicNorms.rootsBar
  have hbij : Function.Bijective (frobenius (Formalism.CyclotomicNorms.Fbar g) g) := PerfectRing.bijective_frobenius
  let F : Formalism.CyclotomicNorms.Fbar g ≃+* Formalism.CyclotomicNorms.Fbar g := RingEquiv.ofBijective (frobenius (Formalism.CyclotomicNorms.Fbar g) g) hbij
  have h1 : ((a.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g))).map (F : Formalism.CyclotomicNorms.Fbar g →+* Formalism.CyclotomicNorms.Fbar g)) =
      a.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) := by
    rw [Polynomial.map_map]
    congr 1
    ext c
    show (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c) ^ g = _
    rw [← map_pow, ZMod.pow_card]
  have h2 := Polynomial.roots_map_of_injective_of_card_eq_natDegree
    (p := a.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g))) (f := (F : Formalism.CyclotomicNorms.Fbar g →+* Formalism.CyclotomicNorms.Fbar g)) F.injective
    (Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits _))
  rw [h1] at h2
  exact h2

end Roots

section Lab

variable (D : D7)
  (hTw : ∀ (k : Fin 2) (w : PlE D.host) (a : D.naut.LP w) (s : ℝ),
    D.naut.items₂ k w (D.naut.lpTw a s) = D.naut.items₂ k w a)

include hTw

theorem inertiaCharpoly_speh_eq_pow (k : Fin 2) (w : PlE D.host) (p : BasicNotions.Part D.naut.CG) :
    D.naut.items₂ k w (spehLoc D.nd D.naut p w) = (D.naut.items₂ k w (D.naut.locG p.π w)) ^ p.d := by
  have key : ∀ l : List ℝ, D.naut.items₂ k w (l.foldr (fun (j : ℝ) acc =>
      D.naut.lpSum (D.naut.lpTw (D.naut.locG p.π w) (((p.d : ℝ) - 1) / 2 - j)) acc) (D.naut.lpZero w)) =
      (D.naut.items₂ k w (D.naut.locG p.π w)) ^ l.length := by
    intro l
    induction l with
    | nil => simp [D.naut.inertiaCharpoly_zero]
    | cons j l ih => rw [List.foldr_cons, D.naut.inertiaCharpoly_add, hTw, ih, List.length_cons, pow_succ, mul_comm]
  unfold spehLoc
  rw [key]
  simp

theorem inertiaCharpoly_eq_of_iso (k : Fin 2) (w : PlE D.host) (Sig : List (BasicNotions.Part D.naut.CG)) :
    D.naut.items₂ k w (isoLoc D.nd D.naut Sig w) =
      (Sig.map fun p => (D.naut.items₂ k w (D.naut.locG p.π w)) ^ p.d).prod := by
  induction Sig with
  | nil => simp [isoLoc, D.naut.inertiaCharpoly_zero]
  | cons p Sig ih =>
    rw [List.map_cons, List.prod_cons, ← ih, ← inertiaCharpoly_speh_eq_pow D hTw]
    exact D.naut.inertiaCharpoly_add _ _ _ _

end Lab

end Formalism.MainNotions.N
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.DimensionInputTwoOfBlochKato
section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions

theorem dimension_input_one_of_bloch_kato (D : D7) (h : Formalism.MainNotions.LocalSituation.Conclusion5 D) : Formalism.MainNotions.BlochKatoDuality.adm1 D := by
  intro l _ K
  exact (h l K).1

theorem dimension_input_two_of_bloch_kato (D : D7) (h : Formalism.MainNotions.LocalSituation.Conclusion5 D) : Formalism.MainNotions.BlochKatoDuality.adm2 D := by
  intro l _ K
  exact (h l K).2.2.2.1

end Formalism.MainNotions.N
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.IrreducibilityOfTheoremThree
section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

open NumberField IsDedekindDomain

def GlobalDatumCompatibility (D : D7) : Prop :=
  Formalism.MainNotions.SphericalInertData.HypEFK D ∧
    (2 ≤ Module.finrank ℚ D.host.F ∧
      ∀ w : PlE D.host, ¬ IsSplitPl D.host w → ((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) ∧
    ∀ j, 1 ≤ j → j ≤ D.R.m → (letI := D.host.cmStar; (D.sp.V j).IsDefinite)

theorem nV_pos (D : D7) : 1 ≤ D.R.nV := by
  have := D.R.t_odd.pos
  show 1 ≤ D.R.r + D.R.t
  omega

theorem hypCM_of (D : D7) (hc : GlobalDatumCompatibility D) : Formalism.MainNotions.SphericalInertData.HypCM D := by
  refine ⟨?_, hc.2.1⟩
  letI := D.host.cmStar
  exact D.sp.cm.cmUnram

theorem base_change_automorphic_of (D : D7) (h45 : Formalism.MainNotions.SphericalInertData.Conclusion1 D) (hc : GlobalDatumCompatibility D) :
    Formalism.MainNotions.SumRepresentations.adm1 D := by
  intro i P
  obtain ⟨Pa, h1, h2, h3, h4, h5, h6⟩ :=
    h45 hc.1 (hypCM_of D hc) (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (nV_pos D)
      (hc.2.2 _ (D.nd.j_range i).1 (D.nd.j_range i).2) (D.nbc.embAV i P)
      (fun w hw => D.nbc.embAV_sph i P w hw)
  refine ⟨Pa, h1, h2, h3, fun w hw => (h4 w hw).trans (D.nbc.embAV_loc i P w).symm,
    fun w hw => ⟨(h5 w hw).1, (h5 w hw).2.trans (congrArg _ (D.nbc.embAV_sat i P w).symm)⟩,
    fun τ => (h6 τ).trans (congrFun (D.nbc.embAV_inf i P) τ).symm⟩

def LitBNIrr (Γ : Type) [Group Γ] : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (a : ℕ) (ρ ρ' : Γ →* GL (Fin a) (Formalism.CyclotomicNorms.Fbar ℓ)),
    (∀ g, ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Formalism.CyclotomicNorms.Fbar ℓ)).charpoly =
      ((ρ' g : GL _ _) : Matrix (Fin a) (Fin a) (Formalism.CyclotomicNorms.Fbar ℓ)).charpoly) →
    Formalism.CyclotomicNorms.IrredOn ρ' ⊤ → Formalism.CyclotomicNorms.IrredOn ρ ⊤

theorem charpoly_mapRep {Γ : Type} [Group Γ] {A B : Type} [CommRing A] [CommRing B] {a : ℕ}
    (f : A →+* B) (ρ : Γ →* GL (Fin a) A) (g : Γ) :
    ((mapRep f ρ g : GL _ _) : Matrix (Fin a) (Fin a) B).charpoly =
      (((ρ g : GL _ _) : Matrix (Fin a) (Fin a) A).charpoly).map f :=
  Matrix.charpoly_map _ f

end Formalism.MainNotions.N
end
end

