module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemPuncturedRingIffPowerSeriesPart
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOfIsMinInClassTwoOfSameClassFour
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AevalArcTxEqZero
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators Topology

namespace GlobalTheory.Ex.ArcForm

theorem hasSum_regroup {X : Type} (e : X → ℤ) (h0 : ∀ χ, 0 ≤ e χ) (hf : ∀ n : ℤ, {χ | e χ = n}.Finite)
    (a : X → ℂ) (u x : ℂ) (h : HasSum (fun χ => u ^ e χ * a χ) x) :
    HasSum (fun n : ℕ => (∑ᶠ (χ : X) (_ : e χ = n), a χ) * u ^ n) x := by
  have h1 := h.tsum_fiberwise fun χ => (e χ).toNat
  refine h1.congr_fun fun n => ?_
  have hs : (fun χ => (e χ).toNat) ⁻¹' {n} = ((hf n).toFinset : Set X) := by
    ext χ
    have := h0 χ
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    omega
  rw [hs, Finset.tsum_subtype' (hf n).toFinset fun χ => u ^ e χ * a χ]
  have h2 : (∑ᶠ (χ : X) (_ : e χ = n), a χ) = ∑ χ ∈ (hf n).toFinset, a χ :=
    finsum_mem_eq_finite_toFinset_sum a (hf n)
  rw [h2, Finset.sum_mul]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  have : e χ = n := by simpa using hχ
  rw [this, zpow_natCast, mul_comm]

theorem finite_fibre {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) {m : ℕ} (hm : m ≠ 0)
    (y : N.X) (n : ℤ) : {χ : N.X | β.be (y + m • χ) (y + m • χ) / (2 * m ^ 2) = n}.Finite := by
  have h := GlobalTheory.ClassMin.finite_sublevel
    (GlobalTheory.ClassMin.realExtension_ofIntBilin_posDef β.symm β.pos) (((n + 1) * (2 * m ^ 2) : ℤ) / 2 : ℝ)
  have hinj : Function.Injective fun χ : N.X => y + m • χ := fun a b hab =>
    smul_right_injective N.X (Int.natCast_ne_zero.2 hm) (by
      simpa only [natCast_zsmul] using add_left_cancel hab)
  refine (h.preimage hinj.injOn).subset fun χ hχ => ?_
  have hχ' : β.be (y + m • χ) (y + m • χ) / (2 * m ^ 2) = n := hχ
  have hpos : (0 : ℤ) < 2 * m ^ 2 := by positivity
  have h2 := Int.lt_ediv_add_one_mul_self (β.be (y + m • χ) (y + m • χ)) hpos
  rw [hχ'] at h2
  simp only [Set.mem_preimage, Set.mem_setOf_eq, GlobalTheory.ClassMin.ofIntBilin_apply]
  have h3 : ((β.be (y + m • χ) (y + m • χ) : ℤ) : ℝ) ≤ (((n + 1) * (2 * m ^ 2) : ℤ) : ℝ) := by
    exact_mod_cast h2.le
  linarith

theorem exponent_nonneg {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) (m : ℕ) (y : N.X) :
    0 ≤ β.be y y / (2 * m ^ 2) := by
  refine Int.ediv_nonneg ?_ (by positivity)
  by_cases h : y = 0
  · simp [h]
  · exact (β.pos y h).le

theorem hasSum_arcTx (N : NumD ℂ) {k : ℕ} (β : N.Form k) {m : ℕ} (hm : m ^ 2 ∣ k) (ho : Odd m)
    (p : N.QT (m ^ 2)) (u : ℂˣ) (h : Summable fun χ => ‖(N.twist β u).txT m (N.twQ β u hm p) χ‖) :
    HasSum (fun n => PowerSeries.coeff n (N.arcTx β.be m p) * (u : ℂ) ^ n)
      ((N.twist β u).tx m (N.twQ β u hm p)) := by
  have h1 : HasSum (fun χ : N.X => (N.twist β u).txT m (N.twQ β u hm p) χ)
      ((N.twist β u).tx m (N.twQ β u hm p)) := h.of_norm.hasSum
  have h2 := hasSum_regroup _ (fun χ => exponent_nonneg β m (p.1.1.toAdd + m • χ))
    (finite_fibre β ho.pos.ne' p.1.1.toAdd) (N.txT m p) u _ (h1.congr_fun fun χ => by
      rw [(GlobalTheory.Ex.twist_terms ℂ N k β u m hm ho p χ).1, Units.val_zpow_eq_zpow_val])
  simpa only [NumD.arcTx, PowerSeries.coeff_mk] using h2

theorem aeval_eq_zero {ι : Type} (f : ι → PowerSeries ℂ) (F : MvPolynomial ι ℂ) {ε : ℝ} (hε : 0 < ε)
    (v : ℂˣ → ι → ℂ) (hs : ∀ u : ℂˣ, ‖(u : ℂ)‖ < ε → ∀ i,
      HasSum (fun n => PowerSeries.coeff n (f i) * (u : ℂ) ^ n) (v u i))
    (hF : ∀ u : ℂˣ, ‖(u : ℂ)‖ < ε → MvPolynomial.eval (v u) F = 0) : MvPolynomial.aeval f F = 0 := by
  have hmem : ∀ i, f i ∈ GlobalTheory.Conv.discSeries ε := fun i u hu => by
    rcases eq_or_ne u 0 with rfl | h0
    · exact summable_of_ne_finset_zero (s := {0}) fun n hn => by
        simp [show n ≠ 0 by simpa using hn]
    · exact (hs (Units.mk0 u h0) hu i).summable
  set G : GlobalTheory.Conv.discSeries ε := MvPolynomial.aeval (fun i => (⟨f i, hmem i⟩ : GlobalTheory.Conv.discSeries ε)) F with hG
  have hGv : (G : PowerSeries ℂ) = MvPolynomial.aeval f F :=
    MvPolynomial.comp_aeval_apply _ (GlobalTheory.Conv.discSeries ε).val F
  rw [← hGv]
  refine GlobalTheory.Conv.eq_zero_of_frequently_sum_eq_zero (GlobalTheory.Conv.discSeries_le_convSeries hε G.2)
    (Filter.Eventually.frequently ?_)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℂ) hε)] with u h0 hu
  have h0' : u ≠ 0 := h0
  have hu' : ‖u‖ < ε := by simpa using hu
  rw [← GlobalTheory.Conv.evalDisc_apply hu', hG, MvPolynomial.comp_aeval_apply, ← hF (Units.mk0 u h0') hu',
    MvPolynomial.aeval_eq_eval]
  congr 2
  funext i
  exact (hs (Units.mk0 u h0') hu' i).tsum_eq

theorem aeval_arcTx_eq_zero : ∀ (N : NumD ℂ) (k : ℕ) (β : N.Form k) (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∀ (ι : Type) (p : ι → N.QT (m ^ 2)) (F : MvPolynomial ι ℂ) (ε : ℝ), 0 < ε → (∀ u : ℂˣ, ‖(u : ℂ)‖ < ε → (∀ i, Summable fun χ => ‖(N.twist β u).txT m (N.twQ β u hm (p i)) χ‖) ∧ MvPolynomial.eval (fun i => (N.twist β u).tx m (N.twQ β u hm (p i))) F = 0) → MvPolynomial.aeval (fun i => N.arcTx β.be m (p i)) F = 0 :=
  fun N _ β m hm ho _ p F _ hε h =>
    aeval_eq_zero _ F hε (fun u i => (N.twist β u).tx m (N.twQ β u hm (p i)))
      (fun u hu i => hasSum_arcTx N β hm ho (p i) u ((h u hu).1 i)) fun u hu => (h u hu).2

end GlobalTheory.Ex.ArcForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataIsoOfTwoWitnesses
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.WitnessData

theorem value_of_genRel {F : Type} [Field F] {B B' B₀ : Scheme.{0}} {M : LB B} {M' : LB B'} {M₀ : LB B₀} {K : Type}
    [Fintype K] {ε : K → ℤ} {φ : B ⟶ B₀} {Φ : B' ⟶ B} {w : LB.Iso M (M₀.pull φ)} {wD : LB.Iso M' (M.pull Φ)}
    {w' : LB.Iso M' (M₀.pull (Φ ≫ φ))} (T : Tri w wD w') (hM₀ : M₀.IsLB) {pt : K → (Sp F ⟶ B)}
    {pt' : K → (Sp F ⟶ B')} {pt₀ : K → (Sp F ⟶ B₀)} (hc : ∀ k, pt' k ≫ Φ = pt k)
    {t : LB.Gen (LB.LinComb M pt ε)} {t' : LB.Gen (LB.LinComb M' pt' ε)} {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} {x : F}
    (h : GenRel w t t₀ x) (h' : GenRel w' t' t₀ x) (z : Sp F) (p : K → M.ι) (q : K → M'.ι)
    (hp : ∀ k, Φ (pt' k z) ∈ M.U (p k)) (hq : ∀ k, pt' k z ∈ M'.U (q k)) :
    gm (𝟙 _) z (LB.wchart M pt p) (t.s p) =
      (∏ k, gw wD (pt' k) z (p k) (q k) ^ ε k) * gm (𝟙 _) z (LB.wchart M' pt' q) (t'.s q) := by
  have pe : ∀ k, pt k z = Φ (pt' k z) := fun k => congrArg (fun g => g z) (hc k).symm
  choose j hj using fun k => exists_chart hM₀ (φ (Φ (pt' k z)))
  have a := T.prod (ε := ε) (h' := 𝟙 _) (fun k => (hc k).trans (Category.id_comp _).symm) _ (𝟙 _) z j p q hj hp hq
  simp only [Category.id_comp] at a
  have b := ((genRel_iff w t t₀ x z).1 h).2 p j (fun k => by rw [pe]; exact hj k) (fun k => by rw [pe]; exact hp k)
  have b' := ((genRel_iff w' t' t₀ x z).1 h').2 q j hj hq
  have e := Units.ext (b.trans b'.symm)
  rw [a, _root_.mul_assoc] at e
  exact mul_left_cancel e

theorem unit_ext_field {K F : Type} [Field K] [Field F] (i : K →+* F) {V : (Sp K).Opens} {a b : Γ(Sp K, V)ˣ}
    (h : ∀ z, spMap i z ∈ V → gm (spMap i) z V a = gm (spMap i) z V b) : a = b := by
  have : QuasiCompact (spMap i) := inferInstanceAs (QuasiCompact (Spec.map _))
  have : IsDominant (spMap i) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 i.injective).le.trans bot_le)⟩
  have : IsReduced (Sp K) := inferInstanceAs (IsReduced (Spec _))
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap i)
  have e : pullU (spMap i) V a = pullU (spMap i) V b := unit_ext fun z hz => by
    rw [gm_pull (𝟙 _) _ z V hz, gm_pull (𝟙 _) _ z V hz, Category.id_comp]
    exact h z hz
  exact Units.ext ((spMap i).app_injective V (congrArg Units.val e))

theorem exists_psi_pull {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {Φ : D'.P.A.left ⟶ D.P.A.left}
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) {W : (Spec (CommRingCat.of R)).Opens} (ψW : PsiOn D W)
    {g : (TK R).left ⟶ (TW W).left} (hg : g ≫ W.ι = jK R) {x : D'.X} {y : D.X} (hx : D'.xK x ≫ Φ = D.xK y)
    (F : Type) [Field F] [Algebra (FractionRing R) F]
    (H : ∀ (z : Sp F) (p : D.P.L.ι) (q : D'.P.L.ι), Φ (D'.xK x (jFK (R := R) F z)) ∈ D.P.L.U p →
      D'.xK x (jFK (R := R) F z) ∈ D'.P.L.U q →
      gm (jFK (R := R) F) z (LB.wchart D.P.L (fun _ : PUnit => D.xK y) (fun _ => p)) ((D.psi y).s (fun _ => p)) =
        gw w (jFK (R := R) F ≫ D'.xK x) z p q ^ (-1 : ℤ) *
          gm (jFK (R := R) F) z (LB.wchart D'.P.L (fun _ : PUnit => D'.xK x) (fun _ => q)) ((D'.psi x).s (fun _ => q))) :
    ∃ b : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => D'.xK x ≫ Φ) (fun _ => -1)),
      GeneratorPullback.MapsAt D.P.L D'.P.L (J := PUnit) (fun _ => Φ) w (D'.xK x) (-1) (D'.psi x) b ∧
      LB.Gen.Corr D.P.L _ _ _ _ b (LB.pullGen D.P.L _ _ (ψW.psi y) g) := by
  have hc : g ≫ (toUnit (TW W) ≫ D.c y).left = D'.xK x ≫ Φ := by
    rw [hx]
    show g ≫ W.ι ≫ (D.c y).left = jK R ≫ (D.c y).left
    rw [← Category.assoc, hg]
  obtain ⟨b, -, vb⟩ := exists_gen D.P.isLB (K' := PUnit) (φ' := fun _ => D'.xK x ≫ Φ) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) hc)
    (LB.pullGen D.P.L _ _ (ψW.psi y) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen y) g)
  refine ⟨b, fun jN jL => ?_, corr_of_val D.P.isLB fun z J hJ => vb _ _ z J hJ⟩
  have hW : jFK (R := R) F ≫ jK R = (jFK (R := R) F ≫ g) ≫ W.ι := by rw [Category.assoc, hg]
  obtain ⟨lam, l₁, l₂⟩ : ∃ lam : Sp F ⟶ (jK R ⁻¹ᵁ W).toScheme, lam ≫ (jK R ⁻¹ᵁ W).ι = jFK (R := R) F ∧
      lam ≫ (jK R ∣_ W) = jFK (R := R) F ≫ g :=
    ⟨(isPullback_morphismRestrict (jK R) W).lift _ _ hW.symm,
      (isPullback_morphismRestrict (jK R) W).lift_snd _ _ _,
      (isPullback_morphismRestrict (jK R) W).lift_fst _ _ _⟩
  refine unit_ext_field (algebraMap (FractionRing R) F) fun z hz => ?_
  have hp : Φ (D'.xK x (jFK (R := R) F z)) ∈ D.P.L.U (jN PUnit.unit) := mem_pull.1 hz.1
  have hq : D'.xK x (jFK (R := R) F z) ∈ D'.P.L.U jL := hz.2
  obtain ⟨J, hJ, eJ⟩ := exists_good D.P.L D.P.isLB z (fun _ : PUnit => jFK (R := R) F ≫ D'.xK x ≫ Φ) jN
    (fun _ _ _ => rfl) (fun _ => hp)
  have v : val b (jFK (R := R) F) z J = val (D.psi y) (jFK (R := R) F) z J := by
    have e := val_corr hJ (ψW.psi_eq y) lam
    rw [val_pull hJ, val_pull hJ, l₁, l₂] at e
    exact (vb _ _ z J hJ).trans ((val_pull hJ _ _ _).trans e)
  rw [val_of b _ z J jN eJ, val_of (D.psi y) _ z J jN (fun k => by rw [← eJ k, hx])] at v
  refine (gm_res _ z _ hz _).trans (v.trans ((H z (jN PUnit.unit) jL hp hq).trans (Eq.symm
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (gm_res _ z _ hz _))))))
  exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull _ _ z _ hz _))

theorem exists_generic_lift {R : Type} [CommRing R] [IsDomain R] {Wo : (Spec (CommRingCat.of R)).Opens}
    (hWo : genericPoint (Spec (CommRingCat.of R)) ∈ Wo) : ∃ g : (TK R).left ⟶ (TW Wo).left, g ≫ Wo.ι = jK R :=
  ⟨IsOpenImmersion.lift Wo.ι (jK R) (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hy : jK R y = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine]
      apply PrimeSpectrum.ext
      show Ideal.comap (algebraMap R (FractionRing R)) (PrimeSpectrum.asIdeal y) = ⊥
      rw [@Ideal.eq_bot_of_prime _ _ (PrimeSpectrum.asIdeal y) (PrimeSpectrum.isPrime y)]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))
    show jK R y ∈ Wo
    rw [hy]; exact hWo), IsOpenImmersion.lift_fac _ _ _⟩

theorem exists_isPullDeg_pre {O' R : Type} [CommRing O'] [IsDomain O'] [CommRing R] [IsDomain R] {f : O' →+* R}
    {D₀ : DegPre O'} {D D' : DegPre R} {φ : D.P.A.left ⟶ D₀.P.A.left} {φ' : D'.P.A.left ⟶ D₀.P.A.left}
    (he : eSec D.P.A ≫ φ = spMap f ≫ eSec D₀.P.A) (he' : eSec D'.P.A ≫ φ' = spMap f ≫ eSec D₀.P.A)
    {w : LB.Iso D.P.L (D₀.P.L.pull φ)} {w' : LB.Iso D'.P.L (D₀.P.L.pull φ')} (ε : D₀.X ≃+ D.X) (ε' : D₀.X ≃+ D'.X)
    (s1 : IsGrpPullback D.P.A D₀.P.A (spMap f) φ) (s1' : IsGrpPullback D'.P.A D₀.P.A (spMap f) φ')
    (s2 : w.IsGen) (s2' : w'.IsGen)
    (s3 : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D.P.A) (fun _ => 1)) D.rig
      (rigPullOf φ (spMap f) he D₀.P.L D₀.rig))
    (s3' : LB.Gen.Maps (LB.linCombIso w' (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
      (rigPullOf φ' (spMap f) he' D₀.P.L D₀.rig))
    (s5 : ∀ y, (D.c (ε y)).left ≫ φ = spMap f ≫ (D₀.c y).left)
    (s5' : ∀ y, (D'.c (ε' y)).left ≫ φ' = spMap f ≫ (D₀.c y).left)
    (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F] (v : D₀.X → F)
    (k : ∀ y, GenRel w (LB.pullGen _ _ _ (D.psi (ε y)) (jFK (R := R) F))
      (LB.pullGen _ _ _ (D₀.psi y) (jFK (R := O') F)) (v y))
    (k' : ∀ y, GenRel w' (LB.pullGen _ _ _ (D'.psi (ε' y)) (jFK (R := R) F))
      (LB.pullGen _ _ _ (D₀.psi y) (jFK (R := O') F)) (v y))
    {Wo : (Spec (CommRingCat.of R)).Opens} (hWo : genericPoint (Spec (CommRingCat.of R)) ∈ Wo) (ψW : PsiOn D Wo) :
    ∃ hD : IsPullDeg (RingHom.id R) D D', (∀ y, hD.xe (ε' y) = ε y) ∧
      ∃ w'' : LB.Iso D'.P.L (D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R))) ≫ φ)),
        φ' = (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R))) ≫ φ ∧ HEq w' w'' ∧ Tri w hD.w w'' := by
  have hs := specOf_id R
  have hsf : specOf (RingHom.id R) ≫ spMap f = spMap f := by rw [hs, Category.id_comp]
  obtain ⟨e, e_hom, hφ⟩ := grpPullback_iso s1'
    (((isGrpPullback_pullback D.P.A (specOf (RingHom.id R))).comp s1).congr hsf rfl)
  let Φ := e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R))
  replace hφ : Φ ≫ φ = φ' := (Category.assoc _ _ _).trans hφ
  subst hφ
  have gp : IsGrpPullback D'.P.A D.P.A (specOf (RingHom.id R)) Φ :=
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback D.P.A (specOf (RingHom.id R)))).congr
      (Category.id_comp _) rfl
  have hE : eSec D'.P.A ≫ Φ = specOf (RingHom.id R) ≫ eSec D.P.A := (cubeMapOf gp).e_comm
  have hw : Φ ≫ D.P.A.hom = D'.P.A.hom := by rw [gp.1.w, hs, Category.comp_id]
  have g0 := (isGen_iff w).1 s2
  have g' := (isGen_iff w').1 s2'
  obtain ⟨wD, T⟩ := exists_cancel D₀.P.isLB w w' g0 g' D.P.isLB D'.P.isLB
  let xe : D'.X ≃+ D.X := ε'.symm.trans ε
  have hxe : ∀ y, xe (ε' y) = ε y := fun y => congrArg ε (ε'.symm_apply_apply y)
  have hc : ∀ y, (D'.c (ε' y)).left ≫ Φ = (D.c (ε y)).left := fun y => by
    apply s1.1.hom_ext
    · rw [Category.assoc, s5' y, s5 y]
    · rw [Category.assoc, hw, Over.w, Over.w]
  obtain ⟨g, hg⟩ := exists_generic_lift hWo
  refine ⟨⟨e, e_hom, wD, (isGen_iff wD).2 (T.pgen_cancel D₀.P.isLB g0 g'), hE, ?_, xe, fun x => ?_, Wo, ψW, g,
    by rw [hg, hs, Category.comp_id], fun x => ?_⟩, hxe, w', rfl, HEq.rfl, T⟩
  · have r₀ := (maps_iff w _ (fun _ => eSec D₀.P.A) _ D.rig D₀.rig (spMap f) _
      (rigPull_le φ (spMap f) he D₀.P.L) (fun _ => rfl)).1 s3
    have r₁ := (maps_iff w' _ (fun _ => eSec D₀.P.A) _ D'.rig D₀.rig (spMap f) _
      (rigPull_le (Φ ≫ φ) (spMap f) he' D₀.P.L) (fun _ => rfl)).1 s3'
    rw [← hsf] at r₁
    exact (maps_iff wD _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf (RingHom.id R)) _
      (rigPull_le Φ (specOf (RingHom.id R)) hE D.P.L) (fun _ => rfl)).2
      (T.pmaps_cancel D₀.P.isLB (fun _ => hE) r₀ r₁)
  · obtain ⟨y, rfl⟩ := ε'.surjective x
    rw [hxe]
    exact (hc y).trans ((Category.id_comp _).symm.trans (congrArg (· ≫ _) hs.symm))
  · obtain ⟨y, rfl⟩ := ε'.surjective x
    rw [hxe]
    have hx : D'.xK (ε' y) ≫ Φ = D.xK (ε y) :=
      (Category.assoc _ _ _).trans (congrArg (jK R ≫ ·) (hc y))
    refine exists_psi_pull wD ψW hg hx F fun z p q hp hq => ?_
    have v := value_of_genRel T D₀.P.isLB (fun _ => (Category.assoc _ _ _).trans (congrArg (jFK (R := R) F ≫ ·) hx))
      (k y) (k' y) z (fun _ => p) (fun _ => q) (fun _ => hp) (fun _ => hq)
    have hp' : D.xK (ε y) (jFK (R := R) F z) ∈ D.P.L.U p :=
      (congrArg (fun h => h (jFK (R := R) F z) ∈ D.P.L.U p) hx).mp hp
    have a₁ := gm_pullGen D.P.L _ _ (D.psi (ε y)) (jFK (R := R) F) (𝟙 _) z (fun _ => p) (Set.mem_iInter.2 fun _ => hp')
    have a₂ := gm_pullGen D'.P.L _ _ (D'.psi (ε' y)) (jFK (R := R) F) (𝟙 _) z (fun _ => q)
      (Set.mem_iInter.2 fun _ => hq)
    rw [Category.id_comp] at a₁ a₂
    rw [Fintype.prod_unique] at v
    exact a₁.symm.trans (v.trans (congrArg _ a₂))

theorem comm_of_pullback {S S₀ : Scheme.{0}} {B B' : Over S} {B₀ : Over S₀} {f : S ⟶ S₀} {i : S ⟶ S} (hi : i = 𝟙 S)
    {φ : B.left ⟶ B₀.left} (hφ : IsPullback φ B.hom B₀.hom f) (e : B' ⟶ (Over.pullback i).obj B)
    {φ' : B'.left ⟶ B₀.left} (hφ' : φ' = (e.left ≫ pullback.fst B.hom i) ≫ φ) {x : B ⟶ B} {x' : B' ⟶ B'}
    {x₀ : B₀.left ⟶ B₀.left} (h : x.left ≫ φ = φ ≫ x₀) (h' : x'.left ≫ φ' = φ' ≫ x₀) :
    x' ≫ e = e ≫ (Over.pullback i).map x := by
  have a : e.left ≫ pullback.snd B.hom i = B'.hom := Over.w e
  have hw : (e.left ≫ pullback.fst B.hom i) ≫ B.hom = B'.hom := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, a, hi, Category.comp_id]
  have e₁ : x'.left ≫ e.left ≫ pullback.fst B.hom i = (e.left ≫ pullback.fst B.hom i) ≫ x.left := by
    apply hφ.hom_ext
    · rw [Category.assoc, ← hφ', h', Category.assoc, h, ← Category.assoc, ← hφ']
    · rw [Category.assoc, hw, Over.w, Category.assoc, Over.w, hw]
  have e₂ : ((Over.pullback i).map x).left ≫ pullback.fst B.hom i = pullback.fst _ _ ≫ x.left :=
    pullback.lift_fst _ _ _
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · show (x'.left ≫ e.left) ≫ _ = (e.left ≫ ((Over.pullback i).map x).left) ≫ _
    rw [Category.assoc, Category.assoc, e₂, ← Category.assoc e.left]
    exact e₁
  · exact (Over.w (x' ≫ e)).trans (Over.w (e ≫ (Over.pullback i).map x)).symm

theorem witness_data_iso : Laws → Laws2 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (I : Ideal R) (f : O' →+* R) (u : R), AdmBase R I → I ≠ ⊤ → Function.Injective f → ∀ (χ χ' : Sp R ⟶ Y.X) (W : ArcWit Y a I f u χ) (W' : ArcWit Y a I f u χ'), ∃ hD : IsPullDeg (RingHom.id R) W.P.D.toPre W'.P.D.toPre, (∀ y, hD.xe (W'.e y) = W.e y) ∧ (∀ x, (letI := H.starRing; W'.P.oD.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (W.P.oD.onB.act x))) ∧ ∃ w' : LB.Iso W'.P.D.toPre.P.L (a.D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (specOf (RingHom.id R))) ≫ W.φ)), W'.φ = (hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (specOf (RingHom.id R))) ≫ W.φ ∧ HEq W'.w w' ∧ Tri W.w hD.w w' := by
  intro _ _ h5 E _ _ _ H D l Xo c W₀ Y O' _ _ _ b a R _ _ _ _ I f u hR _ hf χ χ' W W'
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := W.spec
  obtain ⟨s1', s2', s3', s4', s5', s6'⟩ := W'.spec
  obtain ⟨Wo, hWo, ⟨ψW⟩⟩ := h5.psiOnExists R I hR W.P.D
  let F := AlgebraicClosure (FractionRing R)
  have hi : Function.Injective (((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))).comp f) :=
    ((algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective R _)).comp hf
  letI : Algebra (FractionRing O') F := (IsFractionRing.lift (K := FractionRing O') hi).toAlgebra
  have hF : ∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) =
      algebraMap (FractionRing R) F (algebraMap R _ (f x)) := fun x => IsFractionRing.lift_algebraMap hi x
  obtain ⟨hD, h₁, w', h₂, h₃, h₄⟩ := exists_isPullDeg_pre W.he W'.he W.e.toAddEquiv W'.e.toAddEquiv s1 s1' s2 s2'
    s3 s3' s5 s5' F _ (s6 F _ hF rfl).1 (s6' F _ hF rfl).1 hWo ψW
  exact ⟨hD, h₁, fun x => comm_of_pullback (specOf_id R) s1.1 hD.e.hom h₂ (s4 x) (s4' x), w', h₂, h₃, h₄⟩

end GlobalTheory.WitnessData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMultiplicativeGroupOpenNonvanishingPolynom
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf

noncomputable section
namespace GlobalTheory.SS.TorOpen
open GlobalTheory.SplitTorus ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht

theorem isIso_univPt_left (k : Type) [CommRing k] (X : Type) [AddCommGroup X] :
    IsIso (univPt (A := CommRingCat.of k) X (𝟙 (Sp k))).left := by
  have h1 := GlobalTheory.Diag.isPullback_groupRing k X
  have h2 := GlobalTheory.Diag.isPullback_torusFst (Sp k) X
  have e : (univPt (A := CommRingCat.of k) X (𝟙 (Sp k))).left = (h1.isoIsPullback _ _ h2).hom := by
    apply h2.hom_ext
    · refine Eq.trans ?_ (IsPullback.isoIsPullback_hom_fst _ _ h1 h2).symm
      refine (pullback.lift_fst _ _ _).trans ?_
      rw [Spec.map_comp]
      exact toSpecΓ_SpecMap_ΓSpecIso_inv_assoc (torusRing (CommRingCat.of k) X) _
    · refine Eq.trans ?_ (IsPullback.isoIsPullback_hom_snd _ _ h1 h2).symm
      exact (Over.w _).trans (Category.comp_id _)
  rw [e]; infer_instance

theorem exists_ringHom (k : Type) [Field k] (q : Polynomial k) :
    ∃ ψ : AddMonoidAlgebra k (ULift.{0} ℤ) →+* Localization.Away (Polynomial.X * q),
      IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ)) ∧
      ψ.comp (algebraMap k _) = algebraMap k _ ∧
      ψ (AddMonoidAlgebra.single (ULift.up 1) 1) = algebraMap (Polynomial k) _ Polynomial.X := by
  let L := Localization.Away (Polynomial.X * q)
  have hu : IsUnit (algebraMap (Polynomial k) L Polynomial.X) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := L) (Polynomial.X * q)
    rw [map_mul] at this
    exact isUnit_of_mul_isUnit_left this
  let ψ' : LaurentPolynomial k →+* L := IsLocalization.Away.lift (Polynomial.X : Polynomial k) hu
  have hψ : ψ'.comp (algebraMap (Polynomial k) _) = algebraMap _ _ :=
    IsLocalization.Away.lift_comp _ hu
  let e : AddMonoidAlgebra k (ULift.{0} ℤ) ≃ₐ[k] LaurentPolynomial k :=
    AddMonoidAlgebra.domCongr k k AddEquiv.ulift
  have h1 : IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ')) := by
    have a1 : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (LaurentPolynomial k)))) :=
      IsOpenImmersion.of_isLocalization (Polynomial.X : Polynomial k)
    have a2 : IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ') ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (LaurentPolynomial k)))) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
      exact IsOpenImmersion.of_isLocalization (Polynomial.X * q)
    exact IsOpenImmersion.of_comp _ (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (LaurentPolynomial k))))
  refine ⟨ψ'.comp e.toRingEquiv.toRingHom, ?_, ?_, ?_⟩
  · rw [CommRingCat.ofHom_comp, Spec.map_comp]
    have : IsIso (CommRingCat.ofHom e.toRingEquiv.toRingHom) := e.toRingEquiv.toCommRingCatIso.isIso_hom
    infer_instance
  · ext c
    have : e (algebraMap k _ c) = algebraMap (Polynomial k) _ (algebraMap k _ c) := by
      rw [e.commutes]; simp
    change ψ' (e (algebraMap k _ c)) = _
    rw [this, ← RingHom.comp_apply, hψ, ← IsScalarTower.algebraMap_apply]
  · have : e (AddMonoidAlgebra.single (ULift.up 1) 1) = algebraMap (Polynomial k) _ Polynomial.X := by
      simp [e]; rfl
    change ψ' (e _) = _
    rw [this, ← RingHom.comp_apply, hψ]

theorem exists_of_ringHom (k L : Type) [CommRing k] [CommRing L] [Algebra k L]
    (ψ : AddMonoidAlgebra k (ULift.{0} ℤ) →+* L)
    (h1 : IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ))) (h2 : ψ.comp (algebraMap k _) = algebraMap k _)
    (t : L) (h3 : ψ (AddMonoidAlgebra.single (ULift.up 1) 1) = t) :
    ∃ jj : algOver k L ⟶ Gm (Sp k), IsOpenImmersion jj.left ∧ ∀ x y z : L →ₐ[k] k,
      (algOverHom x ≫ jj) * (algOverHom y ≫ jj) = algOverHom z ≫ jj → x t * y t = z t := by
  have hs : Spec.map (CommRingCat.ofHom (ψ.comp (algebraMap k _))) ≫ 𝟙 (Sp k) =
      spMap (algebraMap k L) := by
    rw [h2]; exact Category.comp_id _
  let jj : algOver k L ⟶ Gm (Sp k) :=
    ptOf (A := CommRingCat.of k) (B := CommRingCat.of L) (𝟙 (Sp k)) ψ hs
  refine ⟨jj, ?_, fun x y z h => ?_⟩
  · have := isIso_univPt_left k (ULift.{0} ℤ)
    exact IsOpenImmersion.comp (Spec.map (CommRingCat.ofHom ψ))
      (univPt (A := CommRingCat.of k) (ULift.{0} ℤ) (𝟙 (Sp k))).left
  · have key : ∀ w : L →ₐ[k] k,
        pull (B := CommRingCat.of k) (s := spMap (algebraMap k k)) (algOverHom w ≫ jj)
          (chi _ (ULift.up 1)) = w t := by
      intro w
      have hs' : Spec.map (CommRingCat.ofHom (((w : L →+* k).comp ψ).comp (algebraMap k _))) ≫ 𝟙 (Sp k) =
          spMap (algebraMap k k) := by
        rw [RingHom.comp_assoc, h2, w.comp_algebraMap]; exact Category.comp_id _
      have e : algOverHom w ≫ jj = ptOf (A := CommRingCat.of k) (B := CommRingCat.of k) (𝟙 (Sp k))
          ((w : L →+* k).comp ψ) hs' := by
        ext1
        change Spec.map (CommRingCat.ofHom (w : L →+* k)) ≫ Spec.map (CommRingCat.ofHom ψ) ≫
            (univPt (A := CommRingCat.of k) (ULift.{0} ℤ) (𝟙 (Sp k))).left =
          Spec.map (CommRingCat.ofHom ((w : L →+* k).comp ψ)) ≫
            (univPt (A := CommRingCat.of k) (ULift.{0} ℤ) (𝟙 (Sp k))).left
        rw [← Category.assoc, ← Spec.map_comp]
        rfl
      rw [e, pull_ptOf, ev_chi]
      exact congrArg w h3
    rw [← key, ← key, ← key, ← h]
    exact (pull_mul_chi (B := CommRingCat.of k) (s := spMap (algebraMap k k)) _ _ _).symm

theorem exists_open_part : ∀ (k : Type) [Field k] (q : Polynomial k), ∃ jj : algOver k (Localization.Away (Polynomial.X * q)) ⟶ Gm (Sp k), IsOpenImmersion jj.left ∧ ∀ x y z : Localization.Away (Polynomial.X * q) →ₐ[k] k, (algOverHom x ≫ jj) * (algOverHom y ≫ jj) = algOverHom z ≫ jj → x (algebraMap (Polynomial k) _ Polynomial.X) * y (algebraMap (Polynomial k) _ Polynomial.X) = z (algebraMap (Polynomial k) _ Polynomial.X) := by
  intro k _ q
  obtain ⟨ψ, h1, h2, h3⟩ := exists_ringHom k q
  exact exists_of_ringHom k _ ψ h1 h2 _ h3

end GlobalTheory.SS.TorOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAffineHomOfIsAffineHomPullbackSndOfFpqc
section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory


open CategoryTheory Limits AlgebraicGeometry in
theorem _root_.GlobalTheory.isAffineHom_of_isAffineHom_pullback_snd_of_fpqc :
    ∀ (X Y Y' : Scheme.{0}) (f : X ⟶ Y) (g : Y' ⟶ Y), Surjective g → Flat g → QuasiCompact g →
      IsAffineHom (pullback.snd f g) → IsAffineHom f := by
  intro X Y Y' f g hs hf hq h
  haveI := _root_.GlobalTheory.isAffineHom_descendsAlong_fpqc
  exact MorphismProperty.DescendsAlong.of_isPullback (P := @IsAffineHom)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (IsPullback.of_hasPullback f g).flip
    ⟨⟨hs, hf⟩, hq⟩ h

end GlobalTheory
end

