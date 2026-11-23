module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0142
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.HermitianCurvature.StatementU
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.Bundle0005
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0159
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0033
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0111
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
public import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0164

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSettingUniformConstantStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_setting_uniform_constant : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq), ∃ c : ℝ, 0 < c ∧ ∀ (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (l : R.H → Wp) (l' : R.H → Wq) (dd : ℝ), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH D.μG R.σ w = dd) → ∀ F s, IsCoef R l l' F s → B.normSq D F = ENNReal.ofReal (c * ‖s‖ ^ 2 / dd) := by
  first | exact @GlobalTheory.BesselNormSq.normSq_coef | exact GlobalTheory.BesselNormSq.normSq_coef | (intros; apply GlobalTheory.BesselNormSq.normSq_coef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenSumLinearCombination
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

theorem capelli_eigenSum_linearCombination : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (lam : Fin (2 * r + k + 1) → ℝ) (d : ℕ) (A : ℝ) (ι : Type) (S : Finset ι) (co : ι → ℂ) (Fs : ι → B.Mat k r → (Wq →L[ℂ] Wp)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), (∀ x ∈ S, ∃ (d' : ℕ) (A' : ℝ), d' ≤ d ∧ A ≤ A' ∧ (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d' : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A') m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (Fs x) g = ∑ i, Fi i g)) → (∀ g ∈ B.GV k r, F g = ∑ x ∈ S, co x • Fs x g) → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (F) g = ∑ i, Fi i g) := by
  intro k r Wp Wq _ _ _ _ _ _ lam d A ι S co Fs F h hF
  classical
  have h' : ∀ x : S, _ := fun x => h x.1 x.2
  choose d' A' hd hA N Fi ν hν hC hE hS using h'
  let e := (Fintype.equivFin (Σ x : S, Fin (N x))).symm
  refine ⟨_, fun j g => co (e j).1 • Fi (e j).1 (e j).2 g, fun j => ν (e j).1 (e j).2, ?_, ?_, ?_, ?_⟩
  · intro j s
    exact (hν _ _ s).trans (by exact_mod_cast hd _)
  · intro j
    refine ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul _ (hC _ _).1, fun m => ?_⟩
    obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.BetaSesquilinearity.sInCC_mono (hA (e j).1) le_rfl ((hC _ (e j).2).2 m)
    exact ⟨_, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul _ hc⟩
  · intro j Y g hg
    have h1 := Formalism.FourierDecayAlt.P.CutMP.En.cV_smul (k := k) (r := r) (Y : ℂ) (co (e j).1) (Fi (e j).1 (e j).2)
    have h2 := congrFun h1 g
    have h3 : (fun g => co (e j).1 • Fi (e j).1 (e j).2 g) = co (e j).1 • Fi (e j).1 (e j).2 := rfl
    beta_reduce
    rw [h3, h2, Pi.smul_apply, hE _ _ Y g hg, smul_comm]
  · intro g hg
    rw [hF g hg, Equiv.sum_comp e (fun y : (Σ x : S, Fin (N x)) => co y.1 • Fi y.1 y.2 g),
      Fintype.sum_sigma, ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hS x g hg, Finset.smul_sum]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryOfSabMap
section
noncomputable section

namespace GlobalTheory.LevelCusp

section Match

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Dict
open scoped Matrix ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

structure IsMatch (X X' : Data E r) (a : GL (Fin r) E) : Prop where
  psi : X.Ψ = X'.Ψ
  p0 : X.p0 = X'.p0
  xi : X.ξ0 = X'.ξ0
  iso : ∀ u v, herm X'.Gm ((a : Matrix (Fin r) (Fin r) E) *ᵥ u) ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm X.Gm u v
  lat : ∀ v, v ∈ X.Λ ↔ (a : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ X'.Λ

theorem isMatch_of_isUStab (X : Data E r) {a : GL (Fin r) E} (h : IsUStab X.Gm X.Λ a) : IsMatch X X a :=
  ⟨rfl, rfl, rfl, h.1, h.2⟩

theorem hermC_of_herm {G G' a : Matrix (Fin r) (Fin r) E} {ε : E}
    (h : ∀ u v, herm G' (a *ᵥ u) (a *ᵥ v) = ε * herm G u v) (τ : E →+* ℂ) (u v : Fin r → ℂ) :
    hermC τ G' (a.map τ *ᵥ u) (a.map τ *ᵥ v) = τ ε * hermC τ G u v := by
  classical
  have key : ∀ i j, ∑ p, ∑ q, τ (a p i) * τ (G' p q) * conj (τ (a q j)) = τ ε * τ (G i j) := fun i j => by
    have := congrArg τ (h (Pi.single i 1) (Pi.single j 1))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [herm, cc, Matrix.mulVec_single_one, Matrix.col_apply, map_sum, map_mul,
      IsCMField.complexEmbedding_complexConj] at this
    rw [this]
    simp [Pi.single_apply, apply_ite, ite_mul]
  have e : hermC τ G' (a.map τ *ᵥ u) (a.map τ *ᵥ v) =
      ∑ j, ∑ i, u i * (∑ p, ∑ q, τ (a p i) * τ (G' p q) * conj (τ (a q j))) * conj (v j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hermC, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun p _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_congr rfl fun p _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  rw [e, Finset.sum_comm]
  simp only [key, hermC, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable {X X' : Data E r} {a : GL (Fin r) E}

theorem IsMatch.mem (h : IsMatch X X' a) (τ : X'.Ψ) : τ.1 ∈ X.Ψ := by rw [h.psi]; exact τ.2

theorem IsMatch.hermC_eq (h : IsMatch X X' a) (τ : E →+* ℂ) (u v : Fin r → ℂ) :
    hermC τ X'.Gm ((a : Matrix (Fin r) (Fin r) E).map τ *ᵥ u) ((a : Matrix (Fin r) (Fin r) E).map τ *ᵥ v) =
      hermC τ X.Gm u v := by
  rw [hermC_of_herm (ε := 1) (fun u v => by rw [h.iso, one_mul]), map_one, one_mul]

theorem IsMatch.dmin_eq (h : IsMatch X X' a) (x : Frame X.Ψ r) (τ : X'.Ψ) (i : Fin (r + 1)) :
    dmin X'.Gm (lact a (castFr h.psi x)) τ i = dmin X.Gm x ⟨τ.1, h.mem τ⟩ i := by
  unfold dmin
  congr 1
  ext p q
  exact h.hermC_eq τ.1 (col (mat x ⟨τ.1, h.mem τ⟩) p) (col (mat x ⟨τ.1, h.mem τ⟩) q)

theorem IsMatch.mem_dom (h : IsMatch X X' a) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    lact a (castFr h.psi x) ∈ X'.dom := fun τ => by
  refine ⟨?_, fun i => by rw [h.dmin_eq, ← h.p0]; exact (hx _).2 i⟩
  have e : mat (lact a (castFr h.psi x)) τ =
      (a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x ⟨τ.1, h.mem τ⟩ := rfl
  rw [e, Matrix.det_mul]
  refine mul_ne_zero ?_ (hx _).1
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, map_ne_zero]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 a.isUnit).ne_zero

end Match

section Exp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UnifPoint GlobalTheory.LevStab
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}
  {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {ty : Fin g → (E →+* ℂ)}

theorem exists_isometry_of_sabMap (F : FamilyUnif Xo σ ty) {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ)
    {i j : Fin F.n} {P : (F.Di i).La →+ (Fin g → ℂ)} {P' : (F.Di j).La →+ (Fin g → ℂ)}
    (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F.Di j) ty P') (hu : F.u i P ≫ ρ = F.u j P') :
    ∃ (gam : (F.Di i).La ≃ₗ[𝓞 E] (F.Di j).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ a b, (F.Di j).EF (gam a) (gam b) = (F.Di i).EF a b) ∧ (∀ a, P' (gam a) = h (P a)) ∧
      ∀ z, (F.ex j P' (h z)).left = (F.ex i P z).left ≫ ν.φ := by
  obtain ⟨β, hβ⟩ := GlobalTheory.CMSpreadCompare.exists_pointEquiv ν.cart (Over.mk (F.u i P)) (s := F.u j P') hu.symm
  have hr : ReadsPeriods Xo.univ.t unitOn (F.Di i) ty P (fun z => β (F.ex i P z)) := by
    refine ⟨fun z => by rw [β.map_eq_one_iff, F.ex_ker i P hP], fun a z => ?_, fun k a b c hk hc => ?_⟩
    · apply Over.OverMorphism.ext
      rw [hβ, F.ex_lin i P hP, Over.comp_left, Over.comp_left, hβ, Category.assoc, Category.assoc]
      exact congrArg _ (ν.act a)
    · obtain ⟨w, hw, -⟩ := ν.lin
      have h₁ := (weilIs_grpPullback_of_comm _ _ Xo.univ.t.G Xo.univ.t.G ρ ν.φ _ _ Xo.univ.t.PP.isLB
        Xo.univ.t.PP.isLB ν.cart ⟨w, hw⟩ _ k _ _ (pushPt ν.cart.1.w _) (pushPt ν.cart.1.w _) _ rfl rfl).1
        (F.ex_weil i P hP k a b c hk hc)
      exact weilIs_congr hu (hβ _).symm (hβ _).symm h₁
  obtain ⟨gam, h, hEF, hh, hx⟩ := exists_isometry_of_hol hP hP' (e := fun z => β (F.ex i P z)) (e' := F.ex j P')
    (fun z w => by rw [F.ex_add i P hP, map_mul]) (β.surjective.comp (F.ex_onto i P hP))
    (by
      simp only [hβ]
      exact GlobalTheory.CMSpreadCompare.isHolTo_postcomp (GlobalTheory.ClassUniq.isHolTo_ex F i P hP) _)
    ⟨F.ex_add j P' hP', F.ex_onto j P' hP', GlobalTheory.ClassUniq.isHolTo_ex F j P' hP', (F.ex_diff j P' hP').1,
      (F.ex_diff j P' hP').2⟩ hr ⟨F.ex_ker j P' hP', F.ex_lin j P' hP', F.ex_weil j P' hP'⟩
  exact ⟨gam, h, hEF, hh, fun z => by rw [hx, hβ]⟩

end Exp

end GlobalTheory.LevelCusp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MarkedLatticeIsometryDoubleCosetMove
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
open GlobalTheory.ShortMove

namespace GlobalTheory.ShortMoveIso

open scoped Matrix

theorem transport {G A : Type} [Group G] [CommRing A] {n : ℕ} (f : G →* GL (Fin n) A)
    (Lh : G → AddSubgroup (Fin n → A)) (hL : ∀ g z, z ∈ Lh g ↔ ∃ y ∈ Lh 1, (f g).1 *ᵥ y = z) (N : ℕ) (δ u k : G)
    (hk : Lh k = Lh 1) :
    (∀ z, z ∈ Lh u ↔ (f δ).1 *ᵥ z ∈ Lh (δ * u * k)) ∧
      ∀ x x' a b, (∃ w ∈ Lh 1, (f k).1 *ᵥ a = b + N • w) → (∃ w ∈ Lh u, x - (f u).1 *ᵥ b = N • w) →
        (∃ w ∈ Lh (δ * u * k), x' - (f (δ * u * k)).1 *ᵥ a = N • w) →
        ∃ w ∈ Lh (δ * u * k), (f δ).1 *ᵥ x - x' = N • w := by
  have hmul : ∀ (a b : G) z, (f (a * b)).1 *ᵥ z = (f a).1 *ᵥ ((f b).1 *ᵥ z) := by
    intro a b z
    rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  have hone : ∀ z, (f 1).1 *ᵥ z = z := by
    intro z
    rw [map_one, Units.val_one, Matrix.one_mulVec]
  have h1 : ∀ z, z ∈ Lh u ↔ (f δ).1 *ᵥ z ∈ Lh (δ * u * k) := by
    intro z
    rw [hL u, hL (δ * u * k)]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨w, hw, rfl⟩ := (hL k y).1 (hk ▸ hy)
      exact ⟨w, hw, by rw [hmul, hmul]⟩
    · rintro ⟨y, hy, h⟩
      refine ⟨(f k).1 *ᵥ y, hk ▸ (hL k _).2 ⟨y, hy, rfl⟩, ?_⟩
      have := congrArg (fun v => (f δ⁻¹).1 *ᵥ v) h
      simp only [← hmul, inv_mul_cancel, hone] at this
      rw [← this, ← hmul, mul_assoc, inv_mul_cancel_left]
  refine ⟨h1, ?_⟩
  rintro x x' a b ⟨y, hy, ey⟩ ⟨w, hw, e⟩ ⟨w', hw', e'⟩
  refine ⟨(f δ).1 *ᵥ w - (f δ).1 *ᵥ ((f u).1 *ᵥ y) - w',
    sub_mem (sub_mem ((h1 w).1 hw) ((h1 _).1 ((hL u _).2 ⟨y, hy, rfl⟩))) hw', ?_⟩
  rw [sub_eq_iff_eq_add.1 e, sub_eq_iff_eq_add.1 e', hmul, hmul, ey]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, smul_sub]
  abel

theorem map_mem_half {R A : Type} [CommRing R] [AddCommGroup A] [Module R A] (I : Ideal R) (s : A →ₗ[R] A) :
    ∀ a ∈ I • (⊤ : Submodule R A), s a ∈ I • (⊤ : Submodule R A) := by
  intro a ha
  refine Submodule.smul_induction_on ha (fun m hm b _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul]
    exact Submodule.smul_mem_smul hm trivial
  · rw [map_add (f := _)]
    exact add_mem hx hy


set_option maxHeartbeats 1000000 in
theorem marked_isometry : ∀ (D : D7) (V : HSp D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (r : ℕ) (hr : V.rank = r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (X X' : Data D.host.E r) (A A' : Datum H) (φ : A.La ≃ₗ[𝓞 D.host.E] X.Λ) (φ' : A'.La ≃ₗ[𝓞 D.host.E] X'.Λ) (t : Dw.La →ₗ[𝓞 D.host.E] A.La) (t' : Dw.La →ₗ[𝓞 D.host.E] A'.La) (s : Dw.La →ₗ[𝓞 D.host.E] Dw.La) (h γ κ : GA D V), ModelW V hr X → ModelW V hr X' → (∀ a b, ((A.EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-X.ξ0 * herm X.Gm (φ a : Fin r → D.host.E) (φ b))) → (∀ a b, ((A'.EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-X'.ξ0 * herm X'.Gm (φ' a : Fin r → D.host.E) (φ' b))) → γ ∈ GQ V → latGHat V κ = latGHat V 1 → (∀ a, ∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (io a)) = finVec V (io (s a)) + l.M • w) → Marked V hr io l X.Λ (fun a => (φ (t a) : Fin r → D.host.E)) h → Marked V hr io l X'.Λ (fun a => (φ' (t' a) : Fin r → D.host.E)) (γ * h * κ) → ∃ gam : A.La ≃ₗ[𝓞 D.host.E] A'.La, (∀ a b, A'.EF (gam a) (gam b) = A.EF a b) ∧ ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ x, gam (t (s a)) = t' a + l.M • x := by
  intro D V H Dw l r hr io X X' A A' φ φ' t t' s h γ κ hW hW' hE hE' hγ hκ hs hm hm'
  subst hr
  obtain ⟨hΛ, hm⟩ := hm
  obtain ⟨hΛ', hm'⟩ := hm'
  obtain ⟨δ, hδu, hδf, -⟩ := GlobalTheory.MarkCoset.rational_matrix V γ hγ
  obtain ⟨ht1, ht2⟩ := transport (finHom V) (latGHat V) (fun g => (GlobalTheory.MarkCoset.latG_spec D V g).2) l.M γ h κ hκ
  have hmem : ∀ v, v ∈ X.Λ ↔ finVec V v ∈ latGHat V h := fun v => by
    rw [← (GlobalTheory.MarkCoset.latG_spec D V h).1, ← SetLike.mem_coe, hΛ]
    exact Set.ext_iff.1 (Set.image_id _) v
  have hmem' : ∀ v, v ∈ X'.Λ ↔ finVec V v ∈ latGHat V (γ * h * κ) := fun v => by
    rw [← (GlobalTheory.MarkCoset.latG_spec D V _).1, ← SetLike.mem_coe, hΛ']
    exact Set.ext_iff.1 (Set.image_id _) v
  have hlat : ∀ v, v ∈ X.Λ ↔ δ.1 *ᵥ v ∈ X'.Λ := fun v => by
    rw [hmem, hmem', ht1, hδf]
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  have hri : ∀ v, δ.1 *ᵥ ((δ⁻¹).1 *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hli : ∀ v, (δ⁻¹).1 *ᵥ (δ.1 *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  let ψ : X.Λ ≃ₗ[𝓞 D.host.E] X'.Λ :=
    { toFun := fun v => ⟨δ.1 *ᵥ v.1, (hlat _).1 v.2⟩
      invFun := fun v => ⟨(δ⁻¹).1 *ᵥ v.1, (hlat _).2 (by rw [hri]; exact v.2)⟩
      map_add' := fun u v => Subtype.ext (Matrix.mulVec_add δ.1 u.1 v.1)
      map_smul' := fun a v => Subtype.ext (Matrix.mulVec_smul δ.1 a v.1)
      left_inv := fun v => Subtype.ext (hli _)
      right_inv := fun v => Subtype.ext (hri _) }
  let gam : A.La ≃ₗ[𝓞 D.host.E] A'.La := φ.trans (ψ.trans φ'.symm)
  have hgam : ∀ a, (φ' (gam a) : Fin V.rank → D.host.E) = δ.1 *ᵥ (φ a : Fin V.rank → D.host.E) := by
    intro a
    simp [gam, ψ]
  have hG : X.Gm = -V.gram.transpose := hW.1
  have hG' : X'.Gm = -V.gram.transpose := hW'.1
  have hξ : X'.ξ0 = X.ξ0 := hW'.2.trans hW.2.symm
  refine ⟨gam, fun a b => ?_, fun a ha => ?_⟩
  · have h1 := hE' (gam a) (gam b)
    rw [hgam, hgam, hG', hξ, hδu, ← hG, ← hE a b] at h1
    exact_mod_cast h1
  · obtain ⟨z, hz, e⟩ := ht2 (finVec V (φ (t (s a)) : Fin V.rank → D.host.E))
      (finVec V (φ' (t' a) : Fin V.rank → D.host.E)) _ _ (hs a) (hm _ (map_mem_half _ s a ha)) (hm' a ha)
    obtain ⟨w, hw, e'⟩ := GlobalTheory.MarkCoset.finVec_div V l.M hM0 (δ.1 *ᵥ (φ (t (s a)) : Fin V.rank → D.host.E) -
      (φ' (t' a) : Fin V.rank → D.host.E)) z (by
        rw [← e, hδf]
        funext i
        exact TensorProduct.tmul_sub _ _ _)
    refine ⟨φ'.symm ⟨w, (hmem' w).2 (hw ▸ hz)⟩, φ'.injective (Subtype.ext ?_)⟩
    rw [hgam, sub_eq_iff_eq_add'.1 e', map_add (f := _), map_nsmul, LinearEquiv.apply_symm_apply]
    rfl

end GlobalTheory.ShortMoveIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorSumPolynomialOperator
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
open scoped ComplexConjugate

namespace GlobalTheory.HatNF.MinorPoly

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem qminor_words (k r m : ℕ) (a b : Fin m → Fin (2 * r + k + 1)) (u : ℂ) :
    ∃ L : List (ℂ × List (B.Mat k r)),
    (∀ cw ∈ L, (∀ X ∈ cw.2, B.inLie k r X) ∧ cw.2.length ≤ m) ∧
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
      B.CkOn ⊤ UU f → ∀ g ∈ UU, g ∈ B.GV k r →
        qminorOp (EabH (Hpk k r)) a b u f g = (L.map fun cw => cw.1 • B.Rw cw.2 f g).sum := by
  let ts : Equiv.Perm (Fin m) → List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) :=
    fun σ => List.ofFn fun j : Fin m => (u - ((j : ℕ) : ℂ), a (σ j), b j)
  refine ⟨(Finset.univ : Finset (Equiv.Perm (Fin m))).toList.flatMap
      (fun σ => (Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand k r (ts σ)).map
        fun cw => (((Equiv.Perm.sign σ : ℤ) : ℂ) * cw.1, cw.2)), ?_, ?_⟩
  · intro cw hcw
    simp only [List.mem_flatMap, List.mem_map] at hcw
    obtain ⟨σ, _, cw', hm', rfl⟩ := hcw
    have := Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand_words (k := k) (r := r) (ts σ) cw' hm'
    refine ⟨fun X hX => (this.1 X hX).1, this.2.trans ?_⟩
    simp [ts]
  · intro E _ _ UU f hf g hgU hg
    have hloc : ∀ σ, Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc ((ts σ).length : ℕ∞) f g := fun σ =>
      Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.loc_mono le_top (hf g hgU)
    have e1 : qminorOp (EabH (Hpk k r)) a b u f g =
        ∑ σ, (((Equiv.Perm.sign σ : ℤ) : ℂ)) • Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT (ts σ) f g := by
      simp only [qminorOp, Finset.sum_apply, Pi.smul_apply]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      congr 1
      simp only [Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT, ts, List.map_ofFn]
      rfl
    rw [e1, Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.sum_flatMap, Finset.sum_map_toList]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand_eq (ts σ) f g hg (hloc σ), List.map_map,
      ← Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.sum_map_mul_smul]
    rfl

section terms

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def scalarTerm (P : B.Mat k r → ℂ) (w : List (B.Mat k r)) (hw : ∀ X ∈ w, B.inLie k r X) : B.DTerm k r Wp Wq where
  coef := fun g => P g • ContinuousLinearMap.id ℂ _
  coefAdj := fun g => star (P g) • ContinuousLinearMap.id ℂ _
  word := w
  word_lie := hw
  adj_id := by
    intro x A B'
    simp only [_root_.smul_apply, ContinuousLinearMap.id_apply]
    rw [Formalism.FourierDecayAlt.P5.HerB.hs_smul_left, Formalism.FourierDecayAlt.P5.HerB.hs_smul_right]
    simp

theorem isPolyDeg_mul_const {N κ : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg κ P) (c : ℂ) :
    U.IsPolyDeg κ fun g => P g * c := by
  obtain ⟨q, hq, he⟩ := h
  refine ⟨q * MvPolynomial.C c, ?_, fun g => by simp [he g]⟩
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  simpa using hq

theorem exists_polyOp_words (m κ : ℕ) (P : B.Mat k r → ℂ) (hP : U.IsPolyDeg κ P)
    (L : List (ℂ × List (B.Mat k r))) (hL : ∀ cw ∈ L, (∀ X ∈ cw.2, B.inLie k r X) ∧ cw.2.length ≤ m) :
    ∃ Θ : B.DiffOp k r Wp Wq, Formalism.FourierDecayAlt.P.CutMP.PolyOp m κ Θ ∧ ∀ F g,
      B.opApply Θ F g = P g • (L.map fun cw => cw.1 • B.Rw cw.2 F g).sum := by
  induction L with
  | nil => exact ⟨[], fun T hT => by simp at hT, fun F g => by simp [B.opApply]⟩
  | cons cw L ih =>
    obtain ⟨Θ, hΘ, he⟩ := ih fun cw' h => hL cw' (List.mem_cons_of_mem _ h)
    have h0 := hL cw List.mem_cons_self
    refine ⟨scalarTerm (fun g => P g * cw.1) cw.2 h0.1 :: Θ, ?_, fun F g => ?_⟩
    · intro T hT
      rcases List.mem_cons.1 hT with rfl | hT
      · exact ⟨h0.2, fun g => P g * cw.1, isPolyDeg_mul_const hP _, fun _ => rfl, fun _ => rfl⟩
      · exact hΘ T hT
    · have h1 := he F g
      simp only [B.opApply, List.map_cons, List.sum_cons] at h1 ⊢
      rw [h1, smul_add, smul_smul]
      rfl

end terms

theorem minor_polyOp : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (k r m κ : ℕ) (ι : Type) [Fintype ι] (a b : ι → Fin m → Fin (2 * r + k + 1)) (u : ℂ) (co : ι → B.Mat k r → ℂ), (∀ i, U.IsPolyDeg κ (co i)) → ∃ Θ : B.DiffOp k r Wp Wq, Formalism.FourierDecayAlt.P.CutMP.PolyOp m κ Θ ∧ ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), ∀ g ∈ B.GV k r, ∀ V : Set (B.Mat k r), IsOpen V → g ∈ V → B.CkOn ⊤ (B.GV k r ∩ V) F → B.opApply Θ F g = ∑ i, co i g • qminorOp (EabH (Hpk k r)) (a i) (b i) u F g := by
  intro Wp Wq _ _ _ _ _ _ k r m κ ι _ a b u co hco
  choose L hL hE using fun i => qminor_words k r m (a i) (b i) u
  choose Θ hΘ hA using fun i => exists_polyOp_words (Wp := Wp) (Wq := Wq) m κ (co i) (hco i) (L i) (hL i)
  refine ⟨(Finset.univ : Finset ι).toList.flatMap Θ, ?_, ?_⟩
  · intro T hT
    obtain ⟨i, _, hi⟩ := List.mem_flatMap.1 hT
    exact hΘ i T hi
  · intro F g hg V _ hgV hF
    unfold B.opApply
    rw [Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.sum_flatMap, Finset.sum_map_toList]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hE i _ _ F hF g ⟨hg, hgV⟩ hg, ← hA i F g]
    rfl

end

end GlobalTheory.HatNF.MinorPoly
end

