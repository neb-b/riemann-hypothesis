module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.RigFrame
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0057
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NumberFieldFinitePlaceCompletionEmbedding

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.MeanSquareMultipleThetaSectionFamily
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameNorm


open GlobalTheory.NormFrame in
set_option maxHeartbeats 1600000 in
theorem ahMean_of_secVal_thetaChar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((F.Di k).La →+ (Fin g → ℂ))) (fr : Xo.univ.t.PP.L.ι → (Fin m → ℂ) × (Fin g → ℂ) → ℂ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (F.Di k).La) (b : Fin m → ℂ) (h τ : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (x : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x)) (κ : ℂ), b ∈ B → IsPeriod (F.Di k) ty (P b) → (∀ v w, (F.Di k).EF (bas v) (bas w) = -omegaStd v w) → IsUnit h.det → τ.IsSymm → (τ.map Complex.im).PosDef → (∀ i, h *ᵥ P b (bas (Pi.single (Sum.inl i) 1)) = Pi.single i 1 ∧ h *ᵥ P b (bas (Pi.single (Sum.inr i) 1)) = τ *ᵥ Pi.single i 1) → (∀ i, c₁ i = 0 ∨ c₁ i = 1 / 2) → (∀ i, c₂ i = 0 ∨ c₂ i = 1 / 2) → RigFrame F k B P fr → x = F.u k (P b) → κ ≠ 0 → SecVal F k (P b) x s (fun z => κ * thetaChar τ c₁ c₂ (h *ᵥ z)) (fun j z => fr j (b, z)) → AHMean F k (P b) x s (‖κ‖ ^ 2 * (Real.sqrt (2 ^ g * (τ.map Complex.im).det))⁻¹) := by
  intro E _ _ _ H Dw l Xo σ' g ty F k m B P fr bas b h τ c₁ c₂ x s κ hbd hper hsympl hdet hsym hpos hn half₁ half₂
    ⟨fr_hol, fr_ne, fr_coc, fr_rig⟩ hx hκ0 hs
  obtain ⟨Hm, hH1, hH2, hH3⟩ := hper.2.2.2.2
  obtain ⟨hHm, -⟩ := GlobalTheory.RiemannForm.herm_eq_of_normalised E H _ g _ bas _ h τ Hm hsympl hper hn
    ⟨hsym, hpos⟩ hH3
  obtain ⟨q, hq⟩ : ∃ q : (Fin g → ℂ) → ℂ, ∀ z, q z = Real.pi / 2 * ((h *ᵥ z) ⬝ᵥ
      (((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) *ᵥ (h *ᵥ z))) := ⟨_, fun _ => rfl⟩
  have hlin : Differentiable ℂ (fun z : Fin g → ℂ => h *ᵥ z) :=
    (Matrix.mulVecLin h).toContinuousLinearMap.differentiable
  have hqd : Differentiable ℂ q := by
    rw [funext hq]
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  have hq0 : q 0 = 0 := by simp [hq]
  obtain ⟨hA1, hA2⟩ := GlobalTheory.ThetaAH.exp_mul_thetaChar_automorphy g τ h Hm c₁ c₂ q hsym hpos
    half₁ half₂ hHm hq
  have hlat : ∀ lam, lam ∈ (P b).range ↔ ∃ m n : Fin g → ℤ,
      h *ᵥ lam = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)) := by
    intro lam
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨v, rfl⟩ := bas.surjective a
      exact ⟨_, _, period_bas bas _ _ _ hn v⟩
    · rintro ⟨m, n, hmn⟩
      refine ⟨bas (Sum.elim m n), ?_⟩
      apply Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hdet)
      rw [hmn]
      exact period_bas bas _ _ _ hn _
  obtain ⟨Fd, hFd, hint⟩ := GlobalTheory.ThetaMean.exists_fundamentalDomain_mean_norm_sq_thetaChar g τ h
    c₁ c₂ _ hsym hpos hdet half₁ half₂ hlat
  obtain ⟨hθd, w0, hw0⟩ := (GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero g c₁ c₂ half₁ half₂).1 _ hsym hpos
  have hχ : ∀ lam : Fin g → ℂ, ∃ χ : ℂ, lam ∈ (P b).range → ‖χ‖ = 1 ∧ ∀ z,
      Complex.exp (q (z + lam)) * thetaChar τ c₁ c₂ (h *ᵥ (z + lam)) =
        χ * Complex.exp (Real.pi * hermForm Hm z lam + Real.pi / 2 * hermForm Hm lam lam) *
          (Complex.exp (q z) * thetaChar τ c₁ c₂ (h *ᵥ z)) := by
    intro lam
    by_cases hl : lam ∈ (P b).range
    · obtain ⟨m, n, hmn⟩ := (hlat lam).1 hl
      obtain ⟨χ, hχ⟩ := hA2 lam m n hmn
      exact ⟨χ, fun _ => hχ⟩
    · exact ⟨1, fun h => absurd h hl⟩
  choose χl hχl using hχ
  have hfrd : ∀ j, DifferentiableOn ℂ (fun z => fr j (b, z) * Complex.exp (-q z))
      {z | ⊤ ≤ (F.ex k (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} := by
    intro j
    refine DifferentiableOn.mul ?_ (by fun_prop)
    exact (fr_hol j).comp (f := fun z => (b, z)) (by fun_prop) fun z hz => ⟨hbd, hz⟩
  have hval : ∀ j z (pt : Sp ℂ ⟶ Gx x),
      pt ≫ gxFst x = (F.ex k (P b) z).left → pt ≫ gxSnd x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex k (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx x).U (fun _ => j)) (s.f (fun _ => j)) =
        (κ * (Complex.exp (q z) * thetaChar τ c₁ c₂ (h *ᵥ z))) *
          (fr j (b, z) * Complex.exp (-q z)) := by
    intro j z pt h1 h2 h3
    rw [hs j z pt h1 h2 h3, Complex.exp_neg]
    have := Complex.exp_ne_zero (q z)
    field_simp
  refine ⟨Hm, χl, fun j z => fr j (b, z) * Complex.exp (-q z),
    fun z => κ * (Complex.exp (q z) * thetaChar τ c₁ c₂ (h *ᵥ z)), Fd, hH1, hH2, hH3, hfrd,
    fun j z hz => mul_ne_zero (fr_ne j b z hbd hz) (Complex.exp_ne_zero _),
    fun j j' z hz => ?_, fun j hz => ?_, fun a j z => ⟨(hχl _ ⟨a, rfl⟩).1, ?_⟩, hval, hFd, ?_⟩
  · beta_reduce
    rw [fr_coc j j' b z hbd hz, mul_assoc]
  · beta_reduce
    rw [hq0, neg_zero, Complex.exp_zero, mul_one, fr_rig j b hbd hz, hx]
  · have hex : ∀ z, F.ex k (P b) (z + P b a) = F.ex k (P b) z :=
      ex_add_period F k _ hper a
    have hO : IsOpen {z | ⊤ ≤ (F.ex k (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} := by
      have h1 := ((F.hol k 0 Set.univ (fun _ => P b) isOpen_univ
        ⟨fun _ _ => hper, fun _ => differentiableOn_const _⟩).2 (Xo.univ.t.PP.L.U j) 0).1
      have h2 := h1.preimage (f := fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) (by fun_prop)
      convert h2 using 1
      ext z
      simp
    refine cancel_entire (θ := fun z => Complex.exp (q z) * thetaChar τ c₁ c₂ (h *ᵥ z))
      (f := fun z => fr j (b, z) * Complex.exp (-q z))
      (f' := fun z => χl (P b a) * Complex.exp (Real.pi * hermForm Hm z (P b a) +
        Real.pi / 2 * hermForm Hm (P b a) (P b a)) *
        (fr j (b, z + P b a) * Complex.exp (-q (z + P b a))))
      ((hqd.cexp).mul (hθd.comp hlin)) ?_ hO (hfrd j).continuousOn ?_ ?_ z
    · obtain ⟨w, hw⟩ := Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hdet) w0
      exact ⟨w, mul_ne_zero (Complex.exp_ne_zero _) (by rw [hw]; exact hw0)⟩
    · refine ContinuousOn.mul (Continuous.continuousOn ?_) ?_
      · simp only [hermForm, dotProduct]
        fun_prop
      · refine (hfrd j).continuousOn.comp (f := fun z => z + P b a) (by fun_prop) fun z hz => ?_
        rw [Set.mem_ofPred_eq, hex]
        exact hz
    · intro z hz
      have hw : 𝟙 _ ≫ x = (F.ex k (P b) z).left ≫ Xo.univ.t.G.hom := by
        rw [Category.id_comp, hx]
        exact (Over.w (F.ex k (P b) z)).symm
      obtain ⟨pt, e₁, e₂⟩ : ∃ pt : Sp ℂ ⟶ Gx x, pt ≫ gxFst x = (F.ex k (P b) z).left ∧ pt ≫ gxSnd x = 𝟙 _ :=
        ⟨pullback.lift (f := x) (g := Xo.univ.t.G.hom) _ _ hw, pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩
      have h1 := hval j z pt e₁ e₂ hz
      have h2 := hval j (z + P b a) pt (by rw [hex]; exact e₁) e₂ (by rw [hex]; exact hz)
      have h3 := h1.symm.trans h2
      rw [(hχl _ ⟨a, rfl⟩).2 z] at h3
      apply mul_left_cancel₀ hκ0
      linear_combination h3
  · rw [← hint, ← mul_div_assoc, ← MeasureTheory.integral_const_mul]
    congr 2
    ext z
    rw [← hA1 z, norm_mul, norm_mul]
    ring

end GlobalTheory.FrameNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ModelChartLiftCoordsGeneratorIndep
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg.LiftUnique

theorem cube_rig_comp {S S' S'' : Scheme.{0}} {G'' : Over S''} {G' : Over S'} {G : Over S} [GrpObj G'']
    [IsCommMonObj G''] [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (m : CubeMap G' G)
    (m' : CubeMap G'' G') (n : CubeMap G'' G) (hF : n.F = m'.F ≫ m.F) (he : n.e = m'.e ≫ m.e)
    (L'' : RigLB G'') (L' : RigLB G') (L : RigLB G) (w : LB.Iso L'.L (L.L.pull m.F))
    (w' : LB.Iso L''.L (L'.L.pull m'.F))
    (hw : w.IsGen ∧ LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig
      (m.rigPull L.L L.rig))
    (hw' : w'.IsGen ∧ LB.Gen.Maps (LB.linCombIso w' (K := PUnit) (fun _ => eSec G'') (fun _ => 1)) L''.rig
      (m'.rigPull L'.L L'.rig)) :
    ∃ w'' : LB.Iso L''.L (L.L.pull n.F),
      (w''.IsGen ∧ LB.Gen.Maps (LB.linCombIso w'' (K := PUnit) (fun _ => eSec G'') (fun _ => 1)) L''.rig
        (n.rigPull L.L L.rig)) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ G''.left) (z : Z) (j : L.L.ι) (i : L'.L.ι) (k : L''.L.ι),
        n.F (r z) ∈ L.L.U j → m'.F (r z) ∈ L'.L.U i → r z ∈ L''.L.U k →
        gw w'' r z j k = gw w (r ≫ m'.F) z j i * gw w' r z i k := by
  obtain ⟨Fn, F3, e, hec, hp⟩ := n
  dsimp only at hF he
  subst hF he
  have g := (isGen_iff w).1 hw.1
  have g' := (isGen_iff w').1 hw'.1
  have r := (maps_iff w _ (fun _ => eSec G) _ L'.rig L.rig m.e _ (rigPull_le m.F m.e m.e_comm L.L)
    (fun _ => rfl)).1 hw.2
  have r' := (maps_iff w' _ (fun _ => eSec G') _ L''.rig L'.rig m'.e _ (rigPull_le m'.F m'.e m'.e_comm L'.L)
    (fun _ => rfl)).1 hw'.2
  obtain ⟨w'', T⟩ := exists_comp L'.isLB w w' g g' L.isLB L''.isLB
  exact ⟨w'', ⟨(isGen_iff w'').2 (T.pgen_comp L'.isLB g g'),
    (maps_iff w'' _ (fun _ => eSec G) _ L''.rig L.rig (m'.e ≫ m.e) _ (rigPull_le _ _ hec L.L) (fun _ => rfl)).2
      (T.pmaps_comp L'.isLB (fun _ => m'.e_comm) r r')⟩, T⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem rig_comp {S S' : Scheme.{0}} {t : SAB H S} {t₁ t₂ : SAB H S'} {f : S' ⟶ S} (m : SABMap t₁ t f)
    (m' : SABMap t₂ t₁ (𝟙 S')) (n : SABMap t₂ t f) (hF : n.φ = m'.φ ≫ m.φ)
    (w : LB.Iso t₁.PP.L (t.PP.L.pull m.φ)) (w' : LB.Iso t₂.PP.L (t₁.PP.L.pull m'.φ)) (hw : RigIso m w)
    (hw' : RigIso m' w') :
    ∃ w'' : LB.Iso t₂.PP.L (t.PP.L.pull n.φ), RigIso n w'' ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ t₂.G.left) (z : Z) (j : t.PP.L.ι) (i : t₁.PP.L.ι) (k : t₂.PP.L.ι),
        n.φ (r z) ∈ t.PP.L.U j → m'.φ (r z) ∈ t₁.PP.L.U i → r z ∈ t₂.PP.L.U k →
        gw w'' r z j k = gw w (r ≫ m'.φ) z j i * gw w' r z i k :=
  cube_rig_comp m.cm m'.cm n.cm hF (by rw [n.base, m.base, m'.base]; exact (Category.id_comp f).symm) _ _ _ w w' hw hw'

theorem exists_over_id {S S' : Scheme.{0}} {t : SAB H S} {t₁ t₂ : SAB H S'} {f f' : S' ⟶ S} (e : f' = 𝟙 _ ≫ f)
    (m : SABMap t₁ t f) (n : SABMap t₂ t f') : ∃ m' : SABMap t₂ t₁ (𝟙 S'), n.φ = m'.φ ≫ m.φ := by
  subst e
  exact sabCancel pullCubCancel E H _ _ _ t t₁ t₂ f (𝟙 _) m n

theorem exists_hom {S S' : Scheme.{0}} {t : SAB H S} {t₁ t₂ : SAB H S'} {f f' : S' ⟶ S} (e : f' = f)
    (m : SABMap t₁ t f) (n : SABMap t₂ t f') : ∃ ψ : t₁.G ⟶ t₂.G, IsMonHom ψ ∧ ψ.left ≫ n.φ = m.φ := by
  subst e
  obtain ⟨ψ, h₁, h₂, -⟩ := sabMap_iso m n rfl rfl
  exact ⟨ψ.hom, h₁, h₂⟩

theorem lieComb_map {R : Type} [CommRing R] {G G' : Over (Sp R)} [GrpObj G] [GrpObj G'] (ψ : G ⟶ G') [IsMonHom ψ]
    {n : ℕ} {c : Fin n → R} {v : Fin n → (epsR R ⟶ G)} {w : epsR R ⟶ G} (h : IsLieComb c v w) :
    IsLieComb c (fun j => v j ≫ ψ) (w ≫ ψ) := by
  obtain ⟨u, hu, rfl⟩ := h
  have hL : ∀ L : List (epsR R ⟶ G), (L.map (· ≫ ψ)).prod = L.prod ≫ ψ := by
    intro L
    induction L with
    | nil => simp [MonObj.one_comp]
    | cons a L ih => rw [List.map_cons, List.prod_cons, List.prod_cons, ih, MonObj.mul_comp]
  refine ⟨fun j => u j ≫ ψ, fun j => ?_, ?_⟩
  · rw [Over.comp_left, Over.comp_left, hu j, Category.assoc]
  · rw [← hL, List.map_ofFn]
    rfl

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β} {M : MChart Y} {R : Type} [CommRing R] [Algebra c.F R] {f : Γ(Y.X, M.U) →+* R}
  {x : Sp R ⟶ Xo.X}

theorem xF_eq (Λ Λ' : M.Lift f x) : Λ'.xF = Λ.xF := by
  apply pullback.hom_ext
  · exact Λ'.xF_fst.trans Λ.xF_fst.symm
  · exact Λ'.xF_snd.trans Λ.xF_snd.symm

theorem vec (Λ Λ' : M.Lift f x) (cv : Fin M.n → R) (w : Sp (DualNumber R) ⟶ Xo.univ.t.G.left) (h : Λ.Vec cv w) :
    Λ'.Vec cv w := by
  obtain ⟨ψ, hψ, e⟩ := exists_hom (xF_eq Λ Λ') Λ.m' Λ'.m'
  obtain ⟨v', u', h₁, h₂, h₃⟩ := h
  have e₁ : ψ.left ≫ Λ'.m1.φ = Λ.m1.φ := by rw [Λ'.liftedChartMap_eq, Λ.liftedChartMap_eq, ← Category.assoc, e]
  have e₂ : ψ.left ≫ Λ'.m2.φ = Λ.m2.φ := by rw [Λ'.matrix_two_by_two_congr, Λ.matrix_two_by_two_congr, ← Category.assoc, e]
  refine ⟨fun j => v' j ≫ ψ, u' ≫ ψ, fun j => ?_, lieComb_map ψ h₂, ?_⟩
  · rw [Over.comp_left, Category.assoc, e₂, h₁ j]
  · rw [Over.comp_left, Category.assoc, e₁, h₃]

theorem thTie (Λ Λ' : M.Lift f x) (s : LB.Sec (PPx x)) (h : Λ.ThTie s) : Λ'.ThTie s := by
  obtain ⟨n, e⟩ := exists_over_id ((xF_eq Λ Λ').trans (Category.id_comp _).symm) Λ.m' Λ'.m'
  have e₁ : Λ'.m1.φ = n.φ ≫ Λ.m1.φ := by rw [Λ'.liftedChartMap_eq, Λ.liftedChartMap_eq, ← Category.assoc, e]
  have e₂ : Λ'.m2.φ = n.φ ≫ Λ.m2.φ := by rw [Λ'.matrix_two_by_two_congr, Λ.matrix_two_by_two_congr, ← Category.assoc, e]
  obtain ⟨w1, w2, σ, s1, r1, r2, i1, c2, c1⟩ := h
  obtain ⟨w0, g0, r0, -⟩ := n.lin
  obtain ⟨w1', r1', T1⟩ := rig_comp Λ.m1 n Λ'.m1 e₁ w1 w0 r1 ⟨g0, r0⟩
  obtain ⟨w2', r2', T2⟩ := rig_comp Λ.m2 n Λ'.m2 e₂ w2 w0 r2 ⟨g0, r0⟩
  have hL := Λ.t'.PP.isLB
  have hL' := Λ'.t'.PP.isLB
  obtain ⟨σ', hσ'⟩ := sec_pull_down ((isGen_iff w0).1 g0) hL hL' σ
  obtain ⟨s1', hs1⟩ := thf_secUp ((isGen_iff w1').1 r1'.1) Xo.univ.t.PP.isLB hL' σ'
  refine ⟨w1', w2', σ', s1', r1', r2', fun (i : PUnit → Xo.univ.t.PP.L.ι) k => fn_ext fun y hy => ?_,
    fun j k W h₁ h₂ => fn_ext fun y hy => ?_, fun g hs hf (j : PUnit → Xo.univ.t.PP.L.ι) hj => fn_ext fun y hy => ?_⟩
  · exact (gs_res _ y _ hy _).trans ((hs1 _ (𝟙 _) y i k hy.1 hy.2).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans
      (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) (gs_res _ y _ hy _)))))
  · obtain ⟨i, hi⟩ := exists_chart hL (n.φ y)
    have hm : Λ.m2.φ (n.φ y) ∈ Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U j :=
      (congrArg (fun q => q y ∈ Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U j) e₂).mp (h₁ hy)
    have hz : (𝟙 _ ≫ n.φ) y ∈ Λ.m2.φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U j) ⊓
        ((Y.t.PP.L.pull Λ.m2.φ).U (fun _ => j) ⊓ Λ.t'.PP.L.U i) := ⟨hm, mem_pull.2 hm.2, hi⟩
    have a := congrArg (gs (𝟙 _ ≫ n.φ) y _) (c2 j i _ inf_le_left inf_le_right)
    have a' : gs ((𝟙 _ ≫ n.φ) ≫ Λ.m2.φ) y _ (M.θ j) =
        (gw w2 (𝟙 _ ≫ n.φ) y j i).val * gs (𝟙 _ ≫ n.φ) y _ (σ.f i) :=
      (gs_appLE Λ.m2.φ _ _ _ _ y hz _).symm.trans (a.trans ((gs_mul _ y _ hz _ _).trans
        (congrArg₂ (· * ·) ((gs_res _ y _ hz _).trans (gs_unit _ y _ hz.2 _)) (gs_res _ y _ hz _))))
    have b := hσ' _ (𝟙 _) y i k hi (h₂ hy).2
    have t := T2 _ (𝟙 _) y j i k (h₁ hy).2 hi (h₂ hy).2
    refine (gs_appLE Λ'.m2.φ _ _ h₁ (𝟙 _) y hy _).trans ?_
    refine (congrArg (fun q => gs q y _ (M.θ j))
      (show 𝟙 _ ≫ Λ'.m2.φ = (𝟙 _ ≫ n.φ) ≫ Λ.m2.φ by rw [e₂, Category.assoc])).trans (a'.trans ?_)
    refine Eq.symm ((gs_mul _ y _ hy _ _).trans ((congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_unit _ y _ (h₂ hy) _).trans (congrArg Units.val t))) (gs_res _ y _ hy _)).trans ?_))
    rw [Units.val_mul, _root_.mul_assoc]
    exact congrArg _ b.symm
  · let A := Xo.univ.t.G
    let a0 : Over.mk (Λ.t'.G.hom ≫ x) ⟶ Over.mk x := Over.homMk Λ.t'.G.hom rfl
    let b0 : Over.mk (Λ.t'.G.hom ≫ x) ⟶ A := Over.homMk Λ.m1.φ Λ.m1.cart.1.w
    let q : Λ.t'.G.left ⟶ Gx x := (lift a0 b0).left
    have qf : q ≫ (fst (Over.mk x) A).left = Λ.t'.G.hom := congrArg (fun q => q.left) (lift_fst a0 b0)
    have qs : q ≫ (snd (Over.mk x) A).left = Λ.m1.φ := congrArg (fun q => q.left) (lift_snd a0 b0)
    have hq : n.φ ≫ q = g := by
      apply pullback.hom_ext
      · rw [Category.assoc]
        show n.φ ≫ q ≫ (fst (Over.mk x) A).left = g ≫ (fst (Over.mk x) A).left
        rw [qf, hf]
        exact n.cart.1.w.trans (Category.comp_id _)
      · rw [Category.assoc]
        show n.φ ≫ q ≫ (snd (Over.mk x) A).left = g ≫ (snd (Over.mk x) A).left
        rw [qs, hs, e₁]
    have le : (Xo.univ.t.PP.L.pull Λ.m1.φ).U j ≤ q ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit) := fun z hz =>
      Set.mem_iInter.2 fun _ => (congrArg (fun p => p z ∈ Xo.univ.t.PP.L.U (j PUnit.unit)) qs).mpr (mem_pull.1 hz)
    obtain ⟨i, hi⟩ := exists_chart hL (n.φ y)
    obtain ⟨k, hk⟩ := exists_chart hL' y
    have hm : Λ.m1.φ (n.φ y) ∈ Xo.univ.t.PP.L.U (j PUnit.unit) :=
      (congrArg (fun p => p y ∈ Xo.univ.t.PP.L.U (j PUnit.unit)) e₁).mp (mem_pull.1 hy)
    have hz : (𝟙 _ ≫ n.φ) y ∈ (Xo.univ.t.PP.L.pull Λ.m1.φ).U j ⊓ Λ.t'.PP.L.U i := ⟨mem_pull.2 hm, hi⟩
    have a := congrArg (gs (𝟙 _ ≫ n.φ) y _) (i1 j i)
    have a' : gs (𝟙 _ ≫ n.φ) y _ (s1.f j) =
        (gw w1 (𝟙 _ ≫ n.φ) y (j PUnit.unit) i).val * gs (𝟙 _ ≫ n.φ) y _ (σ.f i) :=
      (gs_res _ y _ hz _).symm.trans (a.trans ((gs_mul _ y _ hz _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ y _ hz _) (gs_res _ y _ hz _))))
    have b := hσ' _ (𝟙 _) y i k hi hk
    have t := T1 _ (𝟙 _) y (j PUnit.unit) i k (mem_pull.1 hy) hi hk
    have d : gs (𝟙 _ ≫ n.φ) y _ (s1.f j) = gs (𝟙 _ ≫ g) y _ (s.f (fun _ => j PUnit.unit)) :=
      (congrArg (gs (𝟙 _ ≫ n.φ) y _) (c1 q qs qf j le)).trans ((gs_appLE q _ _ le _ y hz.1 _).trans
        (congrArg (fun p => gs p y _ (s.f (fun _ => j PUnit.unit))) (by rw [Category.assoc, hq])))
    refine (hs1 _ (𝟙 _) y j k hy hk).trans (Eq.trans ?_ (a'.symm.trans (d.trans (gs_appLE g _ _ hj (𝟙 _) y hy _).symm)))
    rw [t, Units.val_mul, _root_.mul_assoc]
    exact congrArg _ b.symm

theorem lift_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∀ Λ' : M.Lift f x, (∀ cv w, Λ.Vec cv w → Λ'.Vec cv w) ∧ ∀ s, Λ.ThTie s → Λ'.ThTie s := by
  intro E _ _ _ H Dw l Xo c O _ β Y M R _ _ f x Λ Λ'
  exact ⟨vec Λ Λ', thTie Λ Λ'⟩

end GlobalTheory.Reg.LiftUnique
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.NoCommonZeroOfFiniteValues
section
set_option synthInstance.maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem exists_valuationSubring_hom_of_overLa {K : Type} [Field K] [NumberField K]
    (la : HeightOneSpectrum (𝓞 K)) (T : CDVR) (io : K →+* T.Fr) (e : ℕ) (ho : OverLa la T.V io e) :
    ∃ b : (la.valuation K).valuationSubring →+* T.V,
      (algebraMap T.V T.Fr).comp b = io.comp (la.valuation K).valuationSubring.subtype := by
  have hmem : ∀ a : (la.valuation K).valuationSubring, io a ∈ (algebraMap T.V T.Fr).range := by
    intro a
    apply Formalism.L2.PjFree.mem_range_of_vV_nonneg
    rw [ho.2]
    refine mul_nonneg (by positivity) ?_
    by_cases ha : (a : K) = 0
    · simp [vLa, ha]
    · have hv : la.valuation K (a : K) ≤ 1 := a.2
      have hn : la.valuation K (a : K) ≠ 0 := (la.valuation K).ne_zero_iff.2 ha
      have := (WithZero.log_le_log hn one_ne_zero).2 hv
      simp only [WithZero.log_one] at this
      simp only [vLa]; omega
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  let eq : T.V ≃+* (algebraMap T.V T.Fr).range :=
    RingEquiv.ofBijective (algebraMap T.V T.Fr).rangeRestrict
      ⟨fun x y h => hinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  refine ⟨eq.symm.toRingHom.comp
    ((io.comp (la.valuation K).valuationSubring.subtype).codRestrict _ hmem), ?_⟩
  ext a
  exact congrArg Subtype.val (eq.apply_symm_apply ⟨io a, hmem a⟩)

theorem noCommonZero_of_finite_values : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ la : HeightOneSpectrum (𝓞 c.F), ModelAt Xo c la → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → (∀ v ∈ Formalism.L2.PjFree.valSet Xo c (Formalism.L2.PjFree.algCls Xo c) la, ∃ i, v (ws i) ≠ ⊤) → Formalism.L2.PjFree.NoCommonZero Xo c ws := by
  intro hST E _ _ _ H Dw l Xo c hL la hM a n m ws hws hv k _ _ _ y
  by_contra hcon
  push Not at hcon
  obtain ⟨p, φ, y', hy'⟩ := hL.test k y
  have : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  have hker : ∀ i, evR Xo c (ws i) y' ∈ RingHom.ker φ.toRingHom := by
    intro i
    have := GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n (ws i) (hws i) p.R k φ y' y hy'
    rw [hcon i] at this
    exact this.symm
  obtain ⟨M, hMmax, hle⟩ := Ideal.exists_le_maximal _ (RingHom.ker_ne_top φ.toRingHom)
  let _ : Field (p.R ⧸ M) := Ideal.Quotient.field M
  have : Module.Finite c.F (p.R ⧸ M) := finite_of_finite_type_of_isJacobsonRing c.F (p.R ⧸ M)
  have : NumberField (p.R ⧸ M) := NumberField.of_module_finite c.F (p.R ⧸ M)
  obtain ⟨T, κ, e, ho, hfin⟩ := GlobalTheory.locFld c.F (p.R ⧸ M) (algebraMap c.F (p.R ⧸ M)) la
  set io : c.F →+* T.Fr := κ.comp (algebraMap c.F (p.R ⧸ M)) with hio
  let _ : Algebra c.F T.Fr := io.toAlgebra
  let ψ : p.R →ₐ[c.F] T.Fr := { κ.comp (Ideal.Quotient.mk M) with commutes' := fun _ => rfl }
  obtain ⟨z, hz⟩ := hL.bc p.R T.Fr ψ y'
  have hz0 : ∀ i, evR Xo c (ws i) z = 0 := by
    intro i
    rw [GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n (ws i) (hws i) p.R T.Fr ψ y' z hz]
    show κ (Ideal.Quotient.mk M _) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (hle (hker i)), map_zero]
  obtain ⟨Y, hPI⟩ := hM
  obtain ⟨b, hb⟩ := exists_valuationSubring_hom_of_overLa la T io e ho
  have hIF : IntFramesSt Xo c :=
    intFrames Xo c Out.CubePf.cubePull (lieFree Xo c) (thetaFrame_of Xo c hST) (fun S _ _ y => hL.test S y)
  obtain ⟨w, t, hw⟩ := intFr_of_model hIF T io Y hPI b hb z
  obtain ⟨i, hi⟩ := hv _ ⟨PtV.mk la ho w hfin () trivial, rfl⟩
  apply hi
  show nval T.V e (evI w (ws i)) = ⊤
  have h0 : evI w (ws i) = 0 := by
    have := hL.wt a n (ws i) (hws i) T.Fr t z w.1 ⟨p, ψ, y', hz⟩ w.2.1 hw
    rw [hz0 i, mul_zero] at this
    exact this
  rw [h0, nval_zero]

end GlobalTheory.Reg
end

