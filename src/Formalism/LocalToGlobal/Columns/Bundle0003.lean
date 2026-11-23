module

public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Columns.PolyFn

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.CoefModX
section
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions

def bcLat {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] {n : ℕ} (j : K →+* K')
    (M : Submodule (𝓞 K) (Fin n → K)) : Submodule (𝓞 K') (Fin n → K') :=
  tauLat (fun _ : Unit => j) () M

def bcPol {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] {σ : Type} (j : K →+* K')
    (T : Submodule (𝓞 K) (MvPolynomial σ K)) : Submodule (𝓞 K') (MvPolynomial σ K') :=
  Submodule.span (𝓞 K') ((fun F : MvPolynomial σ K => MvPolynomial.map j F) '' (T : Set (MvPolynomial σ K)))

def polOfVV {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (T : Submodule (𝓞 K) (VV K lam)) : Submodule (𝓞 K) (Pol K ι n) :=
  T.map ((VV K lam).subtype.restrictScalars (𝓞 K))

def BaseChangeSpace : Prop :=
  ∀ (K K' : Type) [Field K] [Field K'] (j : K →+* K') (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n),
    (∀ F : Pol K ι n, F ∈ VV K lam ↔ MvPolynomial.map j F ∈ VV K' lam) ∧
    Submodule.span K' ((fun F : Pol K ι n => MvPolynomial.map j F) '' (VV K lam : Set (Pol K ι n))) = VV K' lam

def BaseChangeAct : Prop :=
  ∀ (K K' : Type) [Field K] [Field K'] (j : K →+* K') (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (g : ι → GL (Fin n) K) (F : Pol K ι n),
    MvPolynomial.map j (actP lam g F) = actP lam (fun τ => Formalism.UG.bc j (g τ)) (MvPolynomial.map j F)

def BaseChangePair : Prop :=
  ∀ (K K' : Type) [Field K] [StarRing K] [Field K'] [StarRing K'] (j : K →+* K'), (∀ x, j (star x) = star (j x)) →
    ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K) (F F' : Pol K ι n),
      pairP lam (fun τ => (G τ).map j) (MvPolynomial.map j F) (MvPolynomial.map j F') = j (pairP lam G F F')

def BaseChangePairV : Prop :=
  ∀ (E K K' : Type) [Field E] [Field K] [StarRing K] [Field K'] [StarRing K'] (j : K →+* K'),
    (∀ x, j (star x) = star (j x)) →
    ∀ (ι : Type) [Fintype ι] (n : ℕ) (emb : ι → E →+* K) (lam : ι → DomWeight n) (J : Matrix (Fin n) (Fin n) E)
      (x x' : VV K lam) (y y' : VV K' lam),
      (y : Pol K' ι n) = MvPolynomial.map j (x : Pol K ι n) → (y' : Pol K' ι n) = MvPolynomial.map j (x' : Pol K ι n) →
      pairV (fun τ => j.comp (emb τ)) lam J y y' = j (pairV emb lam J x x') ∧
      pairVr (fun τ => j.comp (emb τ)) lam J y y' = j (pairVr emb lam J x x')

def BaseChangeTauLat : Prop :=
  ∀ (E K K' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K')
    (ι : Type) (n : ℕ) (emb : ι → E →+* K) (τ : ι) (L : Submodule (𝓞 E) (Fin n → E)),
    tauLat (fun τ => j.comp (emb τ)) τ L = bcLat j (tauLat emb τ L)

def BaseChangeStd : Prop :=
  ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (ι : Type) [Fintype ι] (n : ℕ)
    (lam : ι → DomWeight n), bcPol j (nabStd K lam) = nabStd K' lam ∧ bcPol j (delStd K lam) = delStd K' lam

def NabDelBaseChange : Prop :=
  ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (ι : Type) [Fintype ι] (n : ℕ)
    (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)), (∀ τ, Submodule.IsFullLattice K (M τ)) →
    bcPol j (nabP lam M) = nabP lam (fun τ => bcLat j (M τ)) ∧
    bcPol j (delP lam M) = delP lam (fun τ => bcLat j (M τ))

def NabDelDescent : Prop :=
  ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (ι : Type) [Fintype ι] (n : ℕ)
    (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)), (∀ τ, Submodule.IsFullLattice K (M τ)) →
    ∀ F : Pol K ι n,
      (F ∈ nabP lam M ↔ MvPolynomial.map j F ∈ nabP lam (fun τ => bcLat j (M τ))) ∧
      (F ∈ delP lam M ↔ MvPolynomial.map j F ∈ delP lam (fun τ => bcLat j (M τ)))

def BaseChangeDualFr : Prop :=
  ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (n : ℕ)
    (M : Submodule (𝓞 K) (Fin n → K)), Submodule.IsFullLattice K M → dualFr (bcLat j M) = bcLat j (dualFr M)

def NabDelBaseChangeAt : Prop :=
  ∀ (E K K' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K')
    (ι : Type) [Fintype ι] (n : ℕ) (emb : ι → E →+* K) (lam : ι → DomWeight n) (L : Submodule (𝓞 E) (Fin n → E)),
    Submodule.IsFullLattice E L →
    polOfVV lam (nabAt (fun τ => j.comp (emb τ)) lam L) = bcPol j (polOfVV lam (nabAt emb lam L)) ∧
    polOfVV lam (delAt (fun τ => j.comp (emb τ)) lam L) = bcPol j (polOfVV lam (delAt emb lam L)) ∧
    polOfVV lam (nabAtr (fun τ => j.comp (emb τ)) lam L) = bcPol j (polOfVV lam (nabAtr emb lam L)) ∧
    polOfVV lam (delAtr (fun τ => j.comp (emb τ)) lam L) = bcPol j (polOfVV lam (delAtr emb lam L))

def NabDelDescentAt : Prop :=
  ∀ (E K K' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K')
    (ι : Type) [Fintype ι] (n : ℕ) (emb : ι → E →+* K) (lam : ι → DomWeight n) (L : Submodule (𝓞 E) (Fin n → E)),
    Submodule.IsFullLattice E L → ∀ (x : VV K lam) (y : VV K' lam), (y : Pol K' ι n) = MvPolynomial.map j (x : Pol K ι n) →
    (x ∈ nabAt emb lam L ↔ y ∈ nabAt (fun τ => j.comp (emb τ)) lam L) ∧
    (x ∈ delAt emb lam L ↔ y ∈ delAt (fun τ => j.comp (emb τ)) lam L) ∧
    (x ∈ nabAtr emb lam L ↔ y ∈ nabAtr (fun τ => j.comp (emb τ)) lam L) ∧
    (x ∈ delAtr emb lam L ↔ y ∈ delAtr (fun τ => j.comp (emb τ)) lam L)

end Formalism.L2.DIV
end
end

-- bundled from Formalism.LocalToGlobal.Columns.MtIsoVal
section
noncomputable section

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV

namespace Formalism.L2.Col

section Map

variable {K K' : Type} [Field K] [Field K'] (s : K →+* K')

theorem mti_map_colAddGen {r n : ℕ} (l j : Fin n) (P : MvPolynomial (Fin r × Fin n) K) :
    map s (Formalism.GradedWeylDivisibility.colAddGen K l j P) = Formalism.GradedWeylDivisibility.colAddGen K' l j (map s P) := by
  have h : (map s).comp (Formalism.GradedWeylDivisibility.colAddGen K (r := r) l j).toRingHom =
      (Formalism.GradedWeylDivisibility.colAddGen K' (r := r) l j).toRingHom.comp (map s) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [Formalism.GradedWeylDivisibility.colAddGen]
    · intro v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_X, Formalism.GradedWeylDivisibility.colAddGen, aeval_X]
      split_ifs <;> simp
  exact congrArg (fun φ : MvPolynomial (Fin r × Fin n) K →+* MvPolynomial (Option (Fin r × Fin n)) K' => φ P) h

theorem mti_map_rename_some {r n : ℕ} (P : MvPolynomial (Fin r × Fin n) K) :
    map s (rename (some : Fin r × Fin n → Option (Fin r × Fin n)) P) = rename some (map s P) :=
  map_rename s _ P

theorem mti_map_weighted {r n : ℕ} (ν : Fin n → ℕ) {P : MvPolynomial (Fin r × Fin n) K}
    (hP : P ∈ weightedHomogeneousSubmodule K (Formalism.GradedWeylDivisibility.colW r n) ν) :
    map s P ∈ weightedHomogeneousSubmodule K' (Formalism.GradedWeylDivisibility.colW r n) ν := by
  rw [mem_weightedHomogeneousSubmodule] at hP ⊢
  intro m hm
  rw [coeff_map] at hm
  apply hP
  intro h0
  rw [h0, map_zero] at hm
  exact hm rfl

theorem mti_map_dualWeyl {r n : ℕ} (ν : Fin n → ℕ) {P : MvPolynomial (Fin r × Fin n) K}
    (hP : P ∈ Formalism.GradedWeylDivisibility.dualWeyl K r n ν) : map s P ∈ Formalism.GradedWeylDivisibility.dualWeyl K' r n ν := by
  rw [Formalism.GradedWeylDivisibility.dualWeyl, Submodule.mem_inf] at hP ⊢
  refine ⟨mti_map_weighted s ν hP.1, ?_⟩
  have h2 := hP.2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero] at h2 ⊢
  intro l j hlj
  rw [← mti_map_colAddGen, ← mti_map_rename_some, h2 l j hlj]

end Map

section VVMap

variable {K K' : Type} [Field K] [Field K'] (s : K →+* K') {ι : Type} [Fintype ι] {n : ℕ}

theorem mti_map_ten (F : ι → MvPolynomial (Fin n × Fin n) K) :
    map s (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (F τ)) = ∏ τ, Formalism.GradedWeylDivisibility.blockEmb K' τ (map s (F τ)) := by
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  exact map_rename s _ (F τ)

theorem mti_map_mem_VV (lam : ι → DomWeight n) {F : Pol K ι n} (hF : F ∈ VV K lam) : map s F ∈ VV K' lam := by
  unfold VV Formalism.GradedWeylDivisibility.tensorLat at hF ⊢
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨G, hG, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨fun τ => map s (G τ), fun τ => ?_, mti_map_ten s G⟩
    exact mti_map_dualWeyl s _ (hG τ)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

end VVMap

section RhoMap

variable {K K' : Type} [Field K] [Field K'] (s : K →+* K') {ι : Type} [Fintype ι] {n : ℕ}

end RhoMap

end Formalism.L2.Col
end
end

