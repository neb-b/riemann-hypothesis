module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2448
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalGenerationRatiosClosedFibreAnyUnitSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.AnySec

open MvPolynomial

theorem exists_homog {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} (x : Fin n → S) (j : Fin n) (v : S)
    (hv : x j * v = 1) (F : MvPolynomial (Fin n) R) :
    ∃ (F' : MvPolynomial (Fin n) R) (d : ℕ), eval₂ f (fun l => x l * v) F * x j ^ d = eval₂ f x F' := by
  induction F using MvPolynomial.induction_on with
  | C a => exact ⟨C a, 0, by simp⟩
  | add p q hp hq =>
    obtain ⟨p', dp, ep⟩ := hp
    obtain ⟨q', dq, eq⟩ := hq
    refine ⟨p' * X j ^ dq + q' * X j ^ dp, dp + dq, ?_⟩
    simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X]
    rw [← ep, ← eq]; ring
  | mul_X p l hp =>
    obtain ⟨p', dp, ep⟩ := hp
    refine ⟨p' * X l, dp + 1, ?_⟩
    simp only [eval₂_mul, eval₂_X]
    linear_combination (x l * v * x j) * ep + (x l * eval₂ f x p') * hv

variable {X Y : Scheme.{0}}

theorem isUnit_of_gs {N : X.Opens} (a : Γ(X, N)) (h : ∀ y ∈ N, IsUnit (gs (𝟙 X) y N a)) : IsUnit a :=
  X.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    have := h y hy
    rw [gs_eq (𝟙 X) y N hy] at this
    exact this

theorem gs_rs_app (p : X ⟶ Y) {U : Y.Opens} {N : X.Opens} (hle : N ≤ p ⁻¹ᵁ U) {y : X} (hy : y ∈ N) (a : Γ(Y, U)) :
    gs (𝟙 X) y N (GlobalTheory.AbLaw.rs X hle ((p.app U).hom a)) = gs p y U a := by
  rw [gs_res (𝟙 X) y hle hy, gs_pull (𝟙 X) p y U (hle hy) a, Category.id_comp]

theorem rs_comp_cst {R : Type} [CommRing R] (q : X ⟶ Spec (CommRingCat.of R)) {N N₁ : X.Opens} (hle : N ≤ N₁) :
    (GlobalTheory.AbLaw.rs X hle).comp (GlobalTheory.AbLaw.cst q N₁) = GlobalTheory.AbLaw.cst q N := by
  ext c
  simp only [GlobalTheory.AbLaw.cst, GlobalTheory.AbLaw.rs, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end GlobalTheory.Mum.AnySec

namespace GlobalTheory.Mum.AnySec
open MvPolynomial
variable {X Y : Scheme.{0}}

theorem locGen_anySec_gen {R : Type} [CommRing R] (q : X ⟶ Spec (CommRingCat.of R)) (p : X ⟶ Y) (L : LB Y)
    (k n : ℕ) (τ : Fin n → H0 L k)
    (H : ∀ w : X, ∃ (j : Fin n) (i : Fin 1 → L.ι) (N : X.Opens) (r : Fin n → Γ(X, N)), w ∈ N ∧ IsAffineOpen N ∧
      N ≤ p ⁻¹ᵁ secChart L i ∧ (∀ y ∈ N, IsUnit (secGerm p y (τ j) i) ∧
        ∀ l, secGerm p y (τ l) i = gs (𝟙 _) y N (r l) * secGerm p y (τ j) i) ∧
      ∀ g : Γ(X, N), ∃ P Q : MvPolynomial (Fin n) R, IsUnit (eval₂ (GlobalTheory.AbLaw.cst q N) r Q) ∧
        g * eval₂ (GlobalTheory.AbLaw.cst q N) r Q = eval₂ (GlobalTheory.AbLaw.cst q N) r P)
    (s₀ : H0 L k) (i : Fin 1 → L.ι) (w : X) (hw : p w ∈ secChart L i) (hs : IsUnit (secGerm p w s₀ i)) :
    ∃ (N : X.Opens) (r : Fin n → Γ(X, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ p ⁻¹ᵁ secChart L i ∧
      (∀ y ∈ N, IsUnit (secGerm p y s₀ i) ∧ ∀ l, secGerm p y (τ l) i = gs (𝟙 _) y N (r l) * secGerm p y s₀ i) ∧
      ∀ g : Γ(X, N), ∃ P Q : MvPolynomial (Fin n) R, IsUnit (eval₂ (GlobalTheory.AbLaw.cst q N) r Q) ∧
        g * eval₂ (GlobalTheory.AbLaw.cst q N) r Q = eval₂ (GlobalTheory.AbLaw.cst q N) r P := by
  obtain ⟨j, i', N₁, ρ, hwN, hN₁, hN₁le, hgerm, hgen⟩ := H w
  let V : X.Opens := p ⁻¹ᵁ secChart L i ⊓ X.basicOpen ((p.app (secChart L i)).hom (s₀.f i))
  have hwV : w ∈ V := by
    refine ⟨hw, (Scheme.mem_basicOpen X _ w hw).2 ?_⟩
    have e : secGerm p w s₀ i = _ := gs_eq p w (secChart L i) hw (s₀.f i)
    rw [e] at hs
    exact hs
  obtain ⟨h, hhV, hwh⟩ := hN₁.exists_basicOpen_le ⟨w, hwV⟩ hwN
  have hNN₁ : X.basicOpen h ≤ N₁ := X.basicOpen_le h
  have hNi : X.basicOpen h ≤ p ⁻¹ᵁ secChart L i := hhV.trans inf_le_left
  have hNs : X.basicOpen h ≤ X.basicOpen ((p.app (secChart L i)).hom (s₀.f i)) := hhV.trans inf_le_right
  have hsN : ∀ y ∈ X.basicOpen h, IsUnit (secGerm p y s₀ i) := fun y hy => by
    have := (Scheme.mem_basicOpen _ _ _ (hNi hy)).1 (hNs hy)
    have e : secGerm p y s₀ i = _ := gs_eq p y (secChart L i) (hNi hy) (s₀.f i)
    rw [e]
    exact this
  have hu₀ : IsUnit (GlobalTheory.AbLaw.rs X hNi ((p.app (secChart L i)).hom (s₀.f i))) :=
    isUnit_of_gs _ fun y hy => by rw [gs_rs_app p hNi hy (s₀.f i)]; exact hsN y hy
  obtain ⟨r, hr_def⟩ : ∃ r : Fin n → Γ(X, X.basicOpen h), r = fun l =>
      GlobalTheory.AbLaw.rs X hNi ((p.app (secChart L i)).hom ((τ l).f i)) * (hu₀.unit⁻¹ : (Γ(X, X.basicOpen h))ˣ).val :=
    ⟨_, rfl⟩
  have hr : ∀ y ∈ X.basicOpen h, ∀ l, secGerm p y (τ l) i = gs (𝟙 X) y _ (r l) * secGerm p y s₀ i := by
    intro y hy l
    rw [secGerm, secGerm, ← gs_rs_app p hNi hy ((τ l).f i), ← gs_rs_app p hNi hy (s₀.f i), ← gs_mul _ _ _ hy]
    congr 1
    simp only [hr_def, _root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]
  refine ⟨X.basicOpen h, r, hwh, hN₁.basicOpen h, hNi, fun y hy => ⟨hsN y hy, hr y hy⟩, fun g => ?_⟩

  have key : ∀ y ∈ X.basicOpen h, ∀ l, gs (𝟙 X) y _ (r l) = gs (𝟙 X) y _ (GlobalTheory.AbLaw.rs X hNN₁ (ρ l) * r j) ∧
      IsUnit (gs (𝟙 X) y _ (r j)) := by
    intro y hy l
    have hy₁ := hNN₁ hy
    obtain ⟨c, hc⟩ := exists_unit_secGerm k p y (hNi hy) (hN₁le hy₁)
    have gρ : gs (𝟙 X) y _ (GlobalTheory.AbLaw.rs X hNN₁ (ρ l)) = gs (𝟙 X) y N₁ (ρ l) := gs_res _ _ hNN₁ hy _
    have e1 := hr y hy l
    have e2 := hr y hy j
    have e3 := (hgerm y hy₁).2 l
    have hcl := hc (τ l)
    have hcj := hc (τ j)
    refine ⟨?_, ?_⟩
    · rw [gs_mul _ _ _ hy, gρ]
      apply (hsN y hy).mul_right_cancel
      linear_combination (-1 : _) * e1 + gs (𝟙 X) y N₁ (ρ l) * e2 + hcl - gs (𝟙 X) y N₁ (ρ l) * hcj + c.val * e3
    · have : IsUnit (gs (𝟙 X) y _ (r j) * secGerm p y s₀ i) := by
        rw [← e2, hcj]; exact c.isUnit.mul (hgerm y hy₁).1
      exact isUnit_of_mul_isUnit_left this
  have hrel : ∀ l, r l = GlobalTheory.AbLaw.rs X hNN₁ (ρ l) * r j := fun l => fn_ext fun y hy => (key y hy l).1
  have huj : IsUnit (r j) := isUnit_of_gs _ fun y hy => (key y hy j).2
  let v : Γ(X, X.basicOpen h) := (huj.unit⁻¹ : (Γ(X, X.basicOpen h))ˣ).val
  have hv : r j * v = 1 := IsUnit.mul_val_inv huj
  have hρ : (fun l => GlobalTheory.AbLaw.rs X hNN₁ (ρ l)) = fun l => r l * v := by
    funext l; rw [hrel l, _root_.mul_assoc, hv, _root_.mul_one]

  have hev : ∀ F : MvPolynomial (Fin n) R, GlobalTheory.AbLaw.rs X hNN₁ (eval₂ (GlobalTheory.AbLaw.cst q N₁) ρ F) =
      eval₂ (GlobalTheory.AbLaw.cst q (X.basicOpen h)) (fun l => r l * v) F := fun F => by
    rw [eval₂_comp_left, rs_comp_cst, ← hρ]; rfl
  haveI := hN₁.isLocalization_basicOpen h
  obtain ⟨⟨a, ⟨_, t, rfl⟩⟩, hga⟩ := IsLocalization.surj (Submonoid.powers h) g
  have hhu : IsUnit (GlobalTheory.AbLaw.rs X hNN₁ h) := IsLocalization.Away.algebraMap_isUnit h
  obtain ⟨Pa, Qa, hQa, ea⟩ := hgen a
  obtain ⟨Ph, Qh, hQh, eh⟩ := hgen h
  have ea' := congrArg (GlobalTheory.AbLaw.rs X hNN₁) ea
  have eh' := congrArg (GlobalTheory.AbLaw.rs X hNN₁) eh
  rw [map_mul, hev, hev] at ea' eh'
  have hQh' := hQh.map (GlobalTheory.AbLaw.rs X hNN₁)
  rw [hev] at hQh'
  have hga' : g * GlobalTheory.AbLaw.rs X hNN₁ h ^ t = GlobalTheory.AbLaw.rs X hNN₁ a := by
    rw [← map_pow]; exact hga
  obtain ⟨A', d3, eA⟩ := exists_homog (GlobalTheory.AbLaw.cst q (X.basicOpen h)) r j v hv Pa
  obtain ⟨B', d2, eB⟩ := exists_homog (GlobalTheory.AbLaw.cst q (X.basicOpen h)) r j v hv Qa
  obtain ⟨C', d1, eC⟩ := exists_homog (GlobalTheory.AbLaw.cst q (X.basicOpen h)) r j v hv Ph
  obtain ⟨D', d4, eD⟩ := exists_homog (GlobalTheory.AbLaw.cst q (X.basicOpen h)) r j v hv Qh
  refine ⟨A' * D' ^ t * MvPolynomial.X j ^ (d1 * t + d2), C' ^ t * B' * MvPolynomial.X j ^ (d3 + d4 * t), ?_, ?_⟩
  · simp only [eval₂_mul, eval₂_pow, eval₂_X]
    rw [← eB, ← eC, ← eh']
    have hQa' := hQa.map (GlobalTheory.AbLaw.rs X hNN₁)
    rw [hev] at hQa'
    exact ((((hhu.mul hQh').mul (huj.pow _)).pow _).mul (hQa'.mul (huj.pow _))).mul (huj.pow _)
  · simp only [eval₂_mul, eval₂_pow, eval₂_X]
    rw [← eA, ← eB, ← eC, ← eD, ← eh', ← ea']
    linear_combination (eval₂ (GlobalTheory.AbLaw.cst q (X.basicOpen h)) (fun l => r l * v) Qa *
      eval₂ (GlobalTheory.AbLaw.cst q (X.basicOpen h)) (fun l => r l * v) Qh ^ t * r j ^ (d1 * t + d2 + d3 + d4 * t)) * hga'

end GlobalTheory.Mum.AnySec

theorem GlobalTheory.Mum.locGen_ratio_anySec : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) (L : LB G.left) (k n : ℕ) (τ : Fin n → H0 L k), (∀ w : (thickObj R (maximalIdeal R) 0 G).left, ∃ (j : Fin n) (i : Fin 1 → L.ι) (N : (thickObj R (maximalIdeal R) 0 G).left.Opens) (r : Fin n → Γ((thickObj R (maximalIdeal R) 0 G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ j) i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ j) i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) 0 G).left, N), ∃ P Q : MvPolynomial (Fin n) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r P) → ∀ (s₀ : H0 L k) (i : Fin 1 → L.ι) (w : (thickObj R (maximalIdeal R) 0 G).left), (fstG (maximalIdeal R) 0 G).left w ∈ secChart L i → IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) 0 G).left.Opens) (m : ℕ) (σ : Fin m → H0 L k) (r : Fin m → Γ((thickObj R (maximalIdeal R) 0 G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y s₀ i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (σ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y s₀ i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) 0 G).left, N), ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r P := by
  intro R _ _ _ G L k n τ H s₀ i w hw hs
  obtain ⟨N, r, h1, h2, h3, h4, h5⟩ :=
    GlobalTheory.Mum.AnySec.locGen_anySec_gen ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) _ L k n τ H s₀ i w hw hs
  exact ⟨N, n, τ, r, h1, h2, h3, h4, h5⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatchingExists
section
noncomputable section

namespace GlobalTheory.ThK.Partner

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.BigNZ
open scoped TensorProduct Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Pair

variable {n d : ℕ} {X : Spc F E n} {Y : Spc F E d}

theorem pure_smul (c : ℂ) (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) :
    pure (c • f) φ = c • pure f φ := by
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.smul_apply, smul_eq_mul, Pi.smul_apply, mul_assoc]

theorem polData_sum {B : Base F E} {M : Model σ X Y} {Φ} (h : Φ ∈ PolData B M) :
    ∃ (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol B.ψ B.emb ∧ Fam M (φ i)) ∧ Φ = ∑ i, pure (f i) (φ i) := by
  obtain ⟨m, c, g, e⟩ := Submodule.mem_span_set'.1 h
  choose f hf φ hφ hv hΦ using fun i => (g i).2
  refine ⟨m, fun i => c i • f i, φ, fun i => ⟨Submodule.smul_mem _ _ (hf i), hφ i, hv i⟩, ?_⟩
  rw [← e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pure_smul, ← hΦ i]

theorem finite_bad {M : Model σ X Y} {m : ℕ} {φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ}
    (h : ∀ i, Fam M (φ i)) : {v | ∃ i, φ i v ≠ M.vac v}.Finite := by
  have e : {v | ∃ i, φ i v ≠ M.vac v} = ⋃ i, {v | φ i v ≠ M.vac v} := by ext; simp
  rw [e]
  exact Set.finite_iUnion fun i => eventually_cofinite.1 (h i).2

end Pair

variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
  {R : RealMaps F a a'} {Rf : FinMaps F a a'}

theorem partner_of_big (hK : KP) (hM : IsMatched B G X om om' R Rf) {Φ} (hΦ : Φ ∈ PolData B G.M) :
    ∃ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' := by
  have hco : Coinv B G X om om' Rf := GlobalTheory.T.theta_kernel_coinvariant hK.base F E σ B a a' G X om om' R Rf hM
  obtain ⟨m, f, φ, hfφ, rfl⟩ := polData_sum hΦ
  have hfin := finite_bad fun i => (hfφ i).2
  let T : Finset (Pl F) := X.T ∪ {B.v₁} ∪ hfin.toFinset
  have hXT : X.T ⊆ T := fun v hv => Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  have h1 : B.v₁ ∈ T := Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  have hout : ∀ i, ∀ v ∉ T, φ i v = G.M.vac v := fun i v hv => by
    by_contra hc
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 ⟨i, hc⟩))
  have hre : ∀ i, ∃ g ∈ G.M'.Pol B.ψ B.emb, R.p' g = R.p (f i) := fun i =>
    Submodule.mem_map.1 (hM.real.quot'.onto ▸ Submodule.mem_top)
  choose f' hf' ef using hre
  have hsb : ∀ i v, ∃ χ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Rf.p' v χ = Rf.p v (φ i v) := fun i v =>
    Submodule.mem_map.1 ((hM.fin.onto' v).symm ▸ Submodule.mem_top)
  choose χ hχ eχ using hsb
  have hso : ∀ i, ∃ ζ ∈ G.M'.SoLoc B.ψ B.τ₁, Rf.p' B.v₁ ζ = Rf.p B.v₁ (φ i B.v₁) := fun i =>
    (hco.1 B.v₁ hM.triple.chars.good).2.2.1 B.τ₁ _
  choose ζ hζ eζ using hso
  let φ₀ : Fin m → ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ := fun i v => if v ∈ T then χ i v else G.M'.vac v
  let φ' : Fin m → ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ := fun i => Function.update (φ₀ i) B.v₁ (ζ i)
  have fam₀ : ∀ i, Fam G.M' (φ₀ i) := fun i => by
    refine ⟨fun v => ?_, T.eventually_cofinite_notMem.mono fun v hv => if_neg hv⟩
    by_cases hv : v ∈ T
    · simp only [φ₀, if_pos hv]; exact hχ i v
    · simp only [φ₀, if_neg hv]; exact (hM.triple.geo.hM'.vac v).1
  have fam' : ∀ i, Fam G.M' (φ' i) := fun i => (fam₀ i).update B.v₁ (hζ i).1
  have out' : ∀ i, ∀ v ∉ T, φ' i v = G.M'.vac v := fun i v hv => by
    have hne : v ≠ B.v₁ := fun e => hv (e ▸ h1)
    simp only [φ', Function.update_of_ne hne, φ₀, if_neg hv]
  refine ⟨∑ i, pure (f' i) (φ' i), Submodule.sum_mem _ fun i _ => Submodule.subset_span
    ⟨f' i, φ' i, (fam' i).1, (fam' i).2, by simp only [φ', Function.update_self]; exact hζ i, rfl⟩, ?_⟩
  refine ⟨T, hXT, m, m, f, φ, f', φ', fun i => ⟨(hfφ i).1, (hfφ i).2.1, hout i⟩,
    fun i => ⟨hf' i, (fam' i).1, out' i⟩, rfl, rfl, ?_⟩
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ef i]
  congr 2
  funext ⟨v, hvT⟩
  by_cases hv : v = B.v₁
  · subst hv
    simp only [φ', Function.update_self, eζ]
  · simp only [φ', Function.update_of_ne hv, φ₀, if_pos hvT, eχ]

theorem partner_of_small (hM : IsMatched B G X om om' R Rf) {Φ'} (hΦ' : Φ' ∈ PolData B G.M') :
    ∃ Φ, PolMatch B G X R Rf Φ Φ' := by
  obtain ⟨m, f', φ', hfφ, rfl⟩ := polData_sum hΦ'
  have hfin := finite_bad fun i => (hfφ i).2
  let T : Finset (Pl F) := X.T ∪ hfin.toFinset
  have hXT : X.T ⊆ T := Finset.subset_union_left
  have hout : ∀ i, ∀ v ∉ T, φ' i v = G.M'.vac v := fun i v hv => by
    by_contra hc
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 ⟨i, hc⟩))
  have hre : ∀ i, ∃ g ∈ G.M.Pol B.ψ B.emb, R.p g = R.p' (f' i) := fun i =>
    Submodule.mem_map.1 (hM.real.quot.onto ▸ Submodule.mem_top)
  choose f hf ef using hre
  have hsb : ∀ i v, ∃ χ ∈ SB (Fin a × Fin (a + a') → Fv F v), Rf.p v χ = Rf.p' v (φ' i v) := fun i v =>
    Submodule.mem_map.1 ((hM.fin.onto v).symm ▸ Submodule.mem_top)
  choose χ hχ eχ using hsb
  let φ : Fin m → ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ := fun i v => if v ∈ T then χ i v else G.M.vac v
  have hφ : ∀ i v, φ i v ∈ SB _ := fun i v => by
    by_cases hv : v ∈ T
    · simp only [φ, if_pos hv]; exact hχ i v
    · simp only [φ, if_neg hv]; exact (hM.triple.geo.hM.vac v).1
  refine ⟨∑ i, pure (f i) (φ i), T, hXT, m, m, f, φ, f', φ', fun i => ⟨hf i, hφ i, fun v hv => if_neg hv⟩,
    fun i => ⟨(hfφ i).1, (hfφ i).2.1, hout i⟩, rfl, rfl, ?_⟩
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ef i]
  congr 2
  funext ⟨v, hvT⟩
  simp only [φ, if_pos hvT, eχ]

theorem match_of_polMatch (hM : IsMatched B G X om om' R Rf) {Φ Φ'} (hS : Φ' ∈ G.M'.So B.ψ B.τ₁)
    (h : PolMatch B G X R Rf Φ Φ') : Φ ∈ PolData B G.M ∧ Φ' ∈ PolData B G.M' ∧ Match B G X R Rf Φ Φ' := by
  obtain ⟨T, -, m, m', f, φ, f', φ', hi, hj, e1, e2, -⟩ := id h
  have fam : ∀ i, Fam G.M (φ i) := fun i => ⟨(hi i).2.1, T.eventually_cofinite_notMem.mono (hi i).2.2⟩
  have fam' : ∀ j, Fam G.M' (φ' j) := fun j => ⟨(hj j).2.1, T.eventually_cofinite_notMem.mono (hj j).2.2⟩
  refine ⟨e1 ▸ Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, (hi i).1, φ i, (fam i).1, (fam i).2, rfl⟩,
    e2 ▸ Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨f' j, (hj j).1, φ' j, (fam' j).1, (fam' j).2, rfl⟩,
    hS, m, m', fun i => finPartFn (φ i), f, fun _ => f, fun j => finPartFn (φ' j), f', fun _ => f',
    fun i => ⟨(fam i).sb hM.triple.geo.hM, tendsto_const_nhds⟩, fun j => ⟨(fam' j).sb hM.triple.geo.hM', tendsto_const_nhds⟩,
    e1, e2, fun _ => ⟨?_, ?_⟩⟩
  · show ∑ j, pure (f' j) (φ' j) ∈ _
    rw [← e2]; exact hS
  · show PolMatch B G X R Rf (∑ i, pure (f i) (φ i)) (∑ j, pure (f' j) (φ' j))
    rw [← e1, ← e2]; exact h

end GlobalTheory.ThK.Partner

namespace GlobalTheory.ThK

end GlobalTheory.ThK

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalThetaSectionsRatioCoordinatesOverlap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThBdl

theorem cross_resG_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) {U : Y.Opens} {V W : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (h : W ≤ V) (s : Γ(Y, U)) :
    resG X h ((f.appLE U V e).hom s) = (f.appLE U W (h.trans e)).hom s := by
  rw [← Scheme.Hom.appLE_map f e (homOfLE h).op]
  rfl

theorem cross_resG_resG {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (s : Γ(X, U)) :
    resG X h2 (resG X h1 s) = resG X (h2.trans h1) s := by
  change (X.presheaf.map _ ≫ X.presheaf.map _).hom _ = _
  rw [← Functor.map_comp]
  rfl

theorem cross_resG_self {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (s : Γ(X, U)) : resG X h s = s := by
  change (X.presheaf.map (𝟙 _)).hom s = s
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem cross_appLE_resG {X Y : Scheme.{0}} (f : X ⟶ Y) {U U' : Y.Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (h : U ≤ U') (s : Γ(Y, U')) :
    (f.appLE U V e).hom (resG Y h s) = (f.appLE U' V (e.trans fun _ hx => h hx)).hom s := by
  rw [← Scheme.Hom.map_appLE f e (homOfLE h).op]
  rfl

theorem cross_ratio_val {k Ω : Type} [CommRing k] [Field Ω] {n : ℕ} {x : Sp Ω ⟶ PSpace k n}
    {c : Fin (n + 1) → Ω} (hc : PCrd x c) {U : (PSpace k n).Opens} (hU : ⊤ ≤ x ⁻¹ᵁ U) {a : Fin (n + 1)}
    (ha : U ≤ chart k n a) :
    c a ≠ 0 ∧ ∀ b, (x.appLE U ⊤ hU).hom (ratioOn U a ha b) =
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c b * (c a)⁻¹) := by
  obtain ⟨τ, -, H⟩ := hc
  have h1 : ((O1 k n).pull x).U (fun _ => a) ≤ x ⁻¹ᵁ (O1 k n).U a :=
    LB.wchart_le (O1 k n) (fun _ => x) (fun _ => a) PUnit.unit
  have h2 : ⊤ ≤ ((O1 k n).pull x).U (fun _ => a) :=
    fun y hy => Set.mem_iInter.2 fun _ => ha (hU hy)
  set t : Γ(Sp Ω, ⊤) := resG _ h2 (τ.s (fun _ => a)).val with ht
  have key : ∀ b, (x.appLE U ⊤ hU).hom (ratioOn U a ha b) =
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c b) * t := by
    intro b
    have e := congrArg (resG _ h2) (H b (fun _ => a) h1)
    rw [map_mul, cross_resG_appLE] at e
    have e2 : ratioOn U a ha b = resG _ ha (ratio k n a b) := rfl
    rw [e2, cross_appLE_resG]
    refine e.trans (congrArg (· * t) ?_)
    exact (cross_resG_resG _ _ _).trans (cross_resG_self _ _)
  have ka := key a
  rw [ratioOn_self, map_one] at ka
  have hne : c a ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at ka
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ka
    rw [map_one, map_zero] at this
    exact one_ne_zero (α := Ω) this
  refine ⟨hne, fun b => ?_⟩
  rw [key, map_mul]
  congr 1
  have : (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ *
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a) = 1 := by
    rw [← map_mul]
    exact (congrArg _ (inv_mul_cancel₀ hne)).trans (map_one _)
  calc t = (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ *
      ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a) * t) := by rw [← _root_.mul_assoc, this, _root_.one_mul]
    _ = _ := by rw [← ka, _root_.mul_one]

theorem cross_pull_base {S : Scheme.{0}} (G : Over S) [GrpObj G] {K : Type} [Field K] (ξ : Sp K ⟶ S)
    {N : S.Opens} (hN : ⊤ ≤ ξ ⁻¹ᵁ N) {V : G.left.Opens} (hV : V ≤ G.hom ⁻¹ᵁ N) {W : (Over.mk ξ ⊗ G).left.Opens}
    (hW : W ≤ (snd (Over.mk ξ) G).left ⁻¹ᵁ V) (r : Γ(S, N)) :
    ((snd (Over.mk ξ) G).left.appLE V W hW).hom (resG _ hV ((G.hom.app N).hom r)) =
      liftHom G (T := Over.mk ξ) W ((ξ.appLE N ⊤ hN).hom r) := by
  have e : (snd (Over.mk ξ) G).left ≫ G.hom = (fst (Over.mk ξ) G).left ≫ ξ :=
    (Over.w (snd (Over.mk ξ) G)).trans (Over.w (fst (Over.mk ξ) G)).symm
  have e1 : ((snd (Over.mk ξ) G).left.appLE V W hW).hom (resG _ hV ((G.hom.app N).hom r)) =
      (G.hom.appLE N V hV ≫ (snd (Over.mk ξ) G).left.appLE V W hW).hom r := rfl
  have e2 : liftHom G (T := Over.mk ξ) W ((ξ.appLE N ⊤ hN).hom r) =
      (ξ.appLE N ⊤ hN ≫ (fst (Over.mk ξ) G).left.appLE ⊤ W le_top).hom r := rfl
  rw [e1, e2, Scheme.Hom.appLE_comp_appLE]
  erw [Scheme.Hom.appLE_comp_appLE]
  simp only [e]

theorem cross_ratio_sections : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (G : Over M.Z) [GrpObj G]
    (L : LB G.left) (n : ℕ) (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n) (v : SecM G L 1 (Over.mk M.pt)),
    PCrd (M.pt ≫ h) c →
    (∀ (N N' : M.Z.Opens) (s : LocSec G L N) (s' : LocSec G L N') (w : SecM G L 1 (Over.mk M.pt)),
      GenIs M.pt s w → GenIs M.pt s' w → ∀ i,
        resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N) (s i) =
          resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N') (s' i)) →
    ∀ (a b : Fin (n + 1)) (sa : LocSec G L (h ⁻¹ᵁ chart k n a)) (sb : LocSec G L (h ⁻¹ᵁ chart k n b)),
      (((h ⁻¹ᵁ chart k n a : M.Z.Opens) : Set M.Z).Nonempty →
        GenIs M.pt sa ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ • v)) →
      (((h ⁻¹ᵁ chart k n b : M.Z.Opens) : Set M.Z).Nonempty →
        GenIs M.pt sb ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c b)⁻¹ • v)) →
      ∀ i, resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ :
          L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤ L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n a)) (sa i) =
        resG _ (fun _ hx => hx.2 : L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤
            G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)))
          ((G.hom.app _).hom ((h.app _).hom (ratioOn (chart k n a ⊓ chart k n b) a inf_le_left b))) *
        resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ :
          L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤ L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n b)) (sb i) := by
  intro k Ω _ _ _ M G _ L n c h v hc huniq a b sa sb ha hb i
  by_cases hne : ((h ⁻¹ᵁ (chart k n a ⊓ chart k n b) : M.Z.Opens) : Set M.Z).Nonempty
  swap
  · have hbot : L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) = ⊥ :=
      eq_bot_iff.2 fun y hy => hne ⟨_, hy.2⟩
    have : Subsingleton Γ(G.left, L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b))) := by
      rw [hbot]; infer_instance
    exact Subsingleton.elim _ _
  obtain ⟨ha1, ha2⟩ := ha (hne.mono (show (h ⁻¹ᵁ (chart k n a ⊓ chart k n b) : M.Z.Opens) ≤ h ⁻¹ᵁ chart k n a from fun _ hx => hx.1))
  obtain ⟨hb1, hb2⟩ := hb (hne.mono (show (h ⁻¹ᵁ (chart k n a ⊓ chart k n b) : M.Z.Opens) ≤ h ⁻¹ᵁ chart k n b from fun _ hx => hx.2))
  have htop := M.top_le_preimage_pt hne
  have hr : Set.range M.pt ⊆ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b) : M.Z.Opens) :=
    (top_le_preimage_iff _ _).1 htop
  have htop' : ⊤ ≤ (M.pt ≫ h) ⁻¹ᵁ (chart k n a ⊓ chart k n b) := htop
  obtain ⟨hca, hra⟩ := cross_ratio_val hc htop' inf_le_left
  obtain ⟨hcb, -⟩ := cross_ratio_val hc htop' inf_le_right
  let s₂ : LocSec G L (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) := fun i =>
    resG _ (fun _ hx => hx.2 : L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤
            G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)))
          ((G.hom.app _).hom ((h.app _).hom (ratioOn (chart k n a ⊓ chart k n b) a inf_le_left b))) *
        resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ :
          L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤ L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n b)) (sb i)
  have g₂ : GenIs M.pt s₂ ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ • v) := by
    refine ⟨hr, funext fun j => ?_⟩
    have e3 := congrFun hb2 j
    simp only [genPull, s₂] at e3 ⊢
    rw [map_mul, cross_pull_base G M.pt htop]
    refine (congrArg (_ * ·) ((cross_appLE_resG _ _ _ _).trans e3)).trans ?_
    have e4 : (M.pt.appLE _ ⊤ htop).hom ((h.app _).hom (ratioOn (chart k n a ⊓ chart k n b) a inf_le_left b)) =
        ((M.pt ≫ h).appLE _ ⊤ htop').hom (ratioOn (chart k n a ⊓ chart k n b) a inf_le_left b) := by
      rw [Scheme.Hom.comp_appLE]
      rfl
    rw [e4, hra]
    change liftHom G _ _ * (liftHom G _ _ * v.1 j) = liftHom G _ _ * v.1 j
    rw [← _root_.mul_assoc, ← map_mul]
    congr 2
    erw [← map_mul]
    congr 1
    change c b * (c a)⁻¹ * (c b)⁻¹ = (c a)⁻¹
    field_simp
  have e := congrArg (resG _ (fun _ hx => ⟨hx.1, hx.2.1, hx.2⟩ :
    L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤
      L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n a ⊓ h ⁻¹ᵁ (chart k n a ⊓ chart k n b))))
    (huniq _ _ sa s₂ _ ⟨ha1, ha2⟩ g₂ i)
  exact (cross_resG_resG _ _ _).symm.trans (e.trans ((cross_resG_resG _ _ _).trans (cross_resG_self _ _)))

end GlobalTheory.UMin.ThBdl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordPairingRetractBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordPairingRetract_baseChange : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G₀ : Over S) [GrpObj G₀] [IsCommMonObj G₀] (inc : G ⟶ G₀) (v : G₀ ⟶ G₀) (L : LB G₀.left) (L₁ : LB ((Over.pullback f).obj G₀).left) (P : LB (G2 G).left), L.IsLB → L₁.IsLB → P.IsLB → LBIso L₁ (L.pull (pullback.fst G₀.hom f)) → LBIso P ((abelian₂ G₀ L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ v) : G2 G ⟶ G2 G₀).left) → ∃ π₂ : (G2 ((Over.pullback f).obj G)).left ⟶ (G2 G).left, IsSquare (G' := (Over.pullback f).obj G) (G := G) (pullback.fst G.hom f) π₂ ∧ LBIso ((abelian₂ ((Over.pullback f).obj G₀) L₁).pull (lift (fst _ _ ≫ (Over.pullback f).map inc) (snd _ _ ≫ (Over.pullback f).map inc ≫ (Over.pullback f).map v) : G2 ((Over.pullback f).obj G) ⟶ G2 ((Over.pullback f).obj G₀)).left) (P.pull π₂) := by
  first | exact @GlobalTheory.Mum.lamRetract_baseChange | exact GlobalTheory.Mum.lamRetract_baseChange | (intros; apply GlobalTheory.Mum.lamRetract_baseChange <;> assumption)
end

