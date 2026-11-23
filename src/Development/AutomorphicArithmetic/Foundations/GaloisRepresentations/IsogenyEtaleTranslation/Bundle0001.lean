module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.EtCancel
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PAlFEt
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo

namespace UpperTheory.Gal.FixZ

private theorem act_nat {S : Scheme.{0}} {O : Type} [Ring O] {A : Over S} [GrpObj A] (act : OActN O A) (n : ℕ) :
    act.act (n : O) = (𝟙 A) ^ n := by
  induction n with
  | zero => simp [KS.Model.act_zero]
  | succ n ih => rw [Nat.cast_succ, act.add, ih, act.one, _root_.pow_succ]

private theorem list_prod_ofFn_eq_of_eq_one_of_ne' {M : Type*} [Monoid M] :
    ∀ {m : ℕ} (f : Fin m → M) (i : Fin m), (∀ j, j ≠ i → f j = 1) → (List.ofFn f).prod = f i := by
  intro m
  induction m with
  | zero => intro f i; exact i.elim0
  | succ m ih =>
    intro f i hf
    rw [List.ofFn_succ, List.prod_cons]
    cases i using Fin.cases with
    | zero =>
      rw [List.prod_eq_one, _root_.mul_one]
      intro x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
      exact hf _ (Fin.succ_ne_zero j)
    | succ i =>
      rw [hf 0 (Fin.succ_ne_zero i).symm, _root_.one_mul]
      exact ih (fun j => f j.succ) i (fun j hj => hf _ (fun h => hj (Fin.succ_injective _ h)))

private theorem matEnd_diagonal_pr {S : Scheme.{0}} {O : Type} [Ring O] {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ}
    (d : Fin m → O) (i : Fin m) :
    GlobalTheory.KS.matEnd act (Matrix.diagonal d) ≫ GlobalTheory.KS.pr A i = GlobalTheory.KS.pr A i ≫ act.act (d i) := by
  change (Pi.lift (fun i => (List.ofFn fun j => GlobalTheory.KS.pr A j ≫
    act.act (if i = j then d i else 0)).prod)) ≫ GlobalTheory.KS.pr A i = _
  rw [Pi.lift_comp_π]
  rw [list_prod_ofFn_eq_of_eq_one_of_ne' _ i]
  · simp
  · intro j hj
    simp [Ne.symm hj, KS.Model.act_zero, comp_one]

end UpperTheory.Gal.FixZ

open UpperTheory.Gal.FixZ in
theorem UpperTheory.Gal.FixZ.alFEt_of :
    UpperTheory.Gal.G3.IsogFEt → UpperTheory.Gal.FixZ.PowFEt → UpperTheory.Gal.FixZ.AlFEt := by
  intro hIsog hPow p _ D G L gb k T N α hα
  have hc : ∀ a : 𝓞 D.toG.F, a ≠ 0 → ∃ b : 𝓞 D.toG.F, ∃ d : ℕ, 0 < d ∧ a * b = (d : 𝓞 D.toG.F) := by
    intro a ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
    refine ⟨b, Ideal.absNorm (Ideal.span {a}), Nat.pos_of_ne_zero ?_, ?_⟩
    · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact ha
    · rw [← hb, mul_comm]
  set U := (T.M N).univ with hU
  letI := U.grp
  letI := U.comm
  have key : ∀ x y : 𝓞 D.toG.F, ∀ d : ℕ, x * y = d →
      U.act.act (algebraMap (𝓞 D.toG.F) D.toG.O y) ≫ U.act.act (algebraMap (𝓞 D.toG.F) D.toG.O x)
        = 𝟙 U.A ^ d := by
    intro x y d h
    rw [← U.act.mul, ← map_mul, h, map_natCast, act_nat]
  have hf : ∀ s : Fin k, IsFinite (Over.Hom.left (U.act.act (algebraMap (𝓞 D.toG.F) D.toG.O (α s)))) ∧
      Etale (Over.Hom.left (U.act.act (algebraMap (𝓞 D.toG.F) D.toG.O (α s)))) ∧
      Surjective (Over.Hom.left (U.act.act (algebraMap (𝓞 D.toG.F) D.toG.O (α s)))) := by
    intro s
    obtain ⟨b, d, hd, hab⟩ := hc (α s) (hα s)
    have e1 := key b (α s) d ((mul_comm b (α s)).trans hab)
    have e2 := key (α s) b d hab
    exact hIsog ℂ (T.M N).X (T.M N).s U.A U.A U.ab U.ab _ _ d hd (U.act.hom _) (U.act.hom _) e1 e2
  have hg := hPow _ U.A k (fun s => U.act.act (algebraMap (𝓞 D.toG.F) D.toG.O (α s))) hf
    (KS.matEnd U.act (LocalSmoothExtension.diagO D α)) (fun i => matEnd_diagonal_pr U.act _ i)
  obtain ⟨h1, h2, -⟩ := hg
  show IsFinite ((T.e N).hom ≫ _ ≫ (T.e N).inv) ∧ Etale ((T.e N).hom ≫ _ ≫ (T.e N).inv)
  exact ⟨inferInstance, inferInstance⟩

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PBridge
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo (KS Lv Sc Integ IsTrans)
open UpperTheory.Gal.LocalSmoothExtension (qAt al leg cW CxFin StdC)

namespace UpperTheory.Gal.FixZ

private theorem lev_eq {G : Type} [Group G] (K : Subgroup G) (h : G) :
    GlobalTheory.HeckeCorr.heckeLevel K h⁻¹ = G3.lev K h := by
  ext x
  simp only [GlobalTheory.HeckeCorr.heckeLevel, G3.lev, Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_comap]
  constructor
  · rintro ⟨hx, y, hy, rfl⟩
    refine ⟨hx, ?_⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · rintro ⟨hx, hy⟩
    refine ⟨hx, _, hy, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

private theorem ind_eq {G : Type} [Group G] (K : Subgroup G) (g : G) :
    Formalism.UG.dosetInd ℂ K g = G3.ind ℂ K g := by
  rfl

private theorem smooth_iso {A B C : Scheme.{0}} (e : A ≅ B) (s : B ⟶ C) (n : ℕ)
    (h : SmoothOfRelativeDimension n s) : SmoothOfRelativeDimension n (e.hom ≫ s) := by
  haveI := h
  have := smoothOfRelativeDimension_comp (n := 0) (m := n) e.hom s
  rwa [Nat.zero_add] at this

end UpperTheory.Gal.FixZ

open UpperTheory.Gal UpperTheory.Gal.FixZ in
theorem UpperTheory.Gal.FixZ.bridge_of :
    UpperTheory.Gal.FixZ.TrFEt → UpperTheory.Gal.FixZ.AlFEt → UpperTheory.Gal.FixZ.LegOf → UpperTheory.Gal.FixZ.WtEq → UpperTheory.Gal.FixZ.TanIso → UpperTheory.Gal.FixZ.DimUniq → UpperTheory.Gal.FixZ.CxFinOf → UpperTheory.Gal.FixZ.Bridge := by
  intro hTr hAl hLeg hWt hTan hDim hCx h0 hZ p _ D G L hSc gb hStd i₀ v hv k T N' N hdvd d hsm h a b hreg α hα
  have hτ : ∀ i, D.tau i = D.tau i₀ := fun i => by
    have : Subsingleton (Fin D.a) := by rw [hSc.a1]; infer_instance
    rw [Subsingleton.elim i i₀]
  have hAdm : ∀ u ∈ L.KN N'.1, h * u * h⁻¹ ∈ L.KN N.1 := fun u hu => by
    have := b.2 u (by rw [T.K_eq]; exact hu)
    rwa [T.K_eq] at this
  have hLe : L.KN N'.1 ≤ L.KN N.1 := fun u hu => by
    have := a.2 u (by rw [T.K_eq]; exact hu)
    rw [T.K_eq] at this
    simpa using this
  have hLev : W2.LevOk L N.1 N'.1 h := ⟨N.2.1, N.2.2, N'.2.1, N'.2.2, hdvd, hAdm⟩
  obtain ⟨c₁, hc₁, -⟩ := hLeg p D G L gb k T N' N 1 a
  obtain ⟨c₂, -, hc₂'⟩ := hLeg p D G L gb k T N' N h b
  have hc₂ := hc₂' α
  have hregZ : ∀ g, h * g ∈ L.KN N.1 → GlobalTheory.LKCx.RegAf G g := fun g hg => hreg g (by
    have hm : g ∈ DoubleCoset.doubleCoset h⁻¹ (L.KN N.1 : Set G.GAf) (L.KN N.1) :=
      DoubleCoset.mem_doubleCoset.2 ⟨1, one_mem _, h * g, hg, by simp⟩
    rw [G3.ind, Set.indicator_of_mem hm]
    exact one_ne_zero)
  have heq : ∀ M : Lv p, (T.e M).hom ≫ W2.sZ (T.M M) k = qAt T M := T.e_q
  have hpw : c₁.pw k = (T.e N').inv ≫ T.X.tr _ _ 1 a.1 a.2 ≫ (T.e N).hom := by
    rw [hc₁, Iso.inv_hom_id_assoc]
  have htw : c₂.tw α = (T.e N').inv ≫ leg T N' N h b α ≫ (T.e N).hom := by
    rw [hc₂, Iso.inv_hom_id_assoc]
  have hEt : Etale (c₁.pw k) := by
    haveI := T.X.etale (T.lev N') (T.lev N) a.1 a.2
    rw [hpw]
    infer_instance
  have h₁ : c₁.pw k ≫ W2.sZ (T.M N) k = W2.sZ (T.M N') k := by
    rw [hpw, Category.assoc, Category.assoc, heq N, T.X.tr_q, Iso.inv_comp_eq]
    exact (heq N').symm
  have h₂ : c₂.tw α ≫ W2.sZ (T.M N) k = W2.sZ (T.M N') k := by
    rw [htw, Category.assoc, Category.assoc, heq N, LocalSmoothExtension.leg_q, Iso.inv_comp_eq]
    exact (heq N').symm
  obtain ⟨-, -, -, -, -, hfin, hone, -⟩ := h0 p D G L hSc.a1 hSc.m1 v hv (D.tau i₀) hτ gb hStd N.1 N'.1 h hLev
    (T.M N) (T.M N') c₁ c₂ hregZ k α (fun s => (hα s).2) hEt h₁ h₂
  obtain ⟨hsm₀, Fx, At, hFx, hAt, hSum⟩ := hZ p D G L hSc.a1 hSc.m1 v hv (D.tau i₀) hτ gb hStd N.1 N'.1 h hLev
    (T.M N) (T.M N') c₁ c₂ hregZ k α (fun s => (hα s).2) hEt h₁ h₂
  have hRHS : ∀ y : ℂ, ∑ x ∈ Fx, W2.lefTerm (At x) y =
      (((L.KN N'.1).relIndex (G3.lev (L.KN N.1) h) : ℕ) : ℂ) *
        GlobalTheory.RootSumWeights.cxTotalM G v (cW L i₀ v α y) (L.KN N.1) (G3.ind ℂ (L.KN N.1) h⁻¹) (LocalSmoothExtension.Kp G) (LocalSmoothExtension.oneP G) := by
    intro y
    rw [hSum y, hWt p D G L hSc.a1 i₀ v hv k α y, lev_eq, ind_eq]
    rfl
  have hFT := hTr p D G L gb k T N' N h b.1 b.2
  have hFA := hAl p D G L gb k T N α (fun s => (hα s).1)
  have hlegF : IsFinite (leg T N' N h b α) := by
    haveI := hFT.1
    haveI := hFA.1
    unfold leg
    infer_instance
  have hlegE : Etale (leg T N' N h b α) := by
    haveI := hFT.2
    haveI := hFA.2
    unfold leg
    infer_instance
  refine ⟨hCx p G v (L.KN N.1) (L.KN N'.1) h hLe hAdm hfin hone, hlegF, hlegE, ?_⟩
  by_cases hne : Nonempty (T.X.Z (T.lev N))
  · have hsm₁ : SmoothOfRelativeDimension (D.n - 1 + k * D.g) (qAt T N) := by
      rw [← heq N]
      exact smooth_iso _ _ _ hsm₀
    have hd : d = D.n - 1 + k * D.g := hDim _ (qAt T N) _ _ hsm hsm₁ hne
    subst hd
    obtain ⟨E, -, hE2, hE3⟩ := hTan _ _ _ _ (qAt T N) (qAt T N') (W2.sZ (T.M N) k) (W2.sZ (T.M N') k) (T.e N) (T.e N')
      (heq N) (heq N') (D.n - 1 + k * D.g) (T.X.tr _ _ 1 a.1 a.2) (leg T N' N h b α) (c₁.pw k) (c₂.tw α)
      (T.X.tr_q _ _ 1 a.1 a.2) (LocalSmoothExtension.leg_q T N' N h b α) h₁ h₂ hc₁ hc₂
    have hmem : ∀ x, x ∈ Fx.map E.symm.toEmbedding ↔ E x ∈ Fx := fun x => by
      rw [Finset.mem_map_equiv, Equiv.symm_symm]
    refine ⟨Fx.map E.symm.toEmbedding, fun x => At (E x), fun x => ?_, fun x hx => ?_, fun y => ?_⟩
    · rw [hmem, hFx, hE2]
    · have := hAt _ ((hmem x).1 hx)
      exact ⟨hE3 x _ this.1, this.2⟩
    · rw [← hRHS y, Finset.sum_map]
      simp
  · have hpt : ∀ _ : Sp ℂ ⟶ T.X.Z (T.lev N'), False := fun x =>
      hne ⟨(x ≫ T.X.tr _ _ 1 a.1 a.2) (IsLocalRing.closedPoint ℂ)⟩
    have hFx0 : Fx = ∅ := Finset.eq_empty_of_forall_notMem fun x _ => hpt (x.1 ≫ (T.e N').inv)
    refine ⟨∅, fun _ => 0, fun x => (hpt x.1).elim, fun x => (hpt x.1).elim, fun y => ?_⟩
    rw [← hRHS y, hFx0, Finset.sum_empty, Finset.sum_empty]

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PCxFinOf
section
set_option autoImplicit false

noncomputable section

open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.FixZ.ComplexFinitenessOfFixed

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p} {v : InfinitePlace G.F}

private abbrev SameB (v : InfinitePlace G.F) (B : GlobalTheory.LKCx.Form G) (Kf : Subgroup G.GAf) :
    GlobalTheory.LKCx.Dat G v B.β → GlobalTheory.LKCx.Dat G v B.β → Prop :=
  GlobalTheory.LKCx.Same G v B.β B.trivAf.choose B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec Kf
    (KHT p G.m G.n 1 G.Fw)

private def shf {β : G.Cˣ} (a : GlobalTheory.LKCx.Dat G v β) (k : G.GAf) : GlobalTheory.LKCx.Dat G v β := ((a.1.1 * k, a.1.2), a.2)

private theorem toV_mul' {β : G.Cˣ} (y y' : GlobalTheory.LKCx.grp G β) (z : Fin G.n → ℂ) :
    ((GlobalTheory.LKCx.toV G v β (y * y') : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z =
      (GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ
        ((GlobalTheory.LKCx.toV G v β y' : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) := by
  rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]

private theorem toV_inv' {β : G.Cˣ} (y : GlobalTheory.LKCx.grp G β) (z : Fin G.n → ℂ) :
    (GlobalTheory.LKCx.toV G v β y⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ
      ((GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) = z := by
  rw [← toV_mul', inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec]

private theorem same_symm' {B : GlobalTheory.LKCx.Form G} {Kf : Subgroup G.GAf} {a b : GlobalTheory.LKCx.Dat G v B.β}
    (h : SameB v B Kf a b) : SameB v B Kf b a := by
  obtain ⟨y, k, c, hk1, hk2, hc, h1, h2⟩ := h
  refine ⟨y⁻¹, k⁻¹, c⁻¹, Kf.inv_mem hk1, (KHT p G.m G.n 1 G.Fw).inv_mem hk2, inv_ne_zero hc, ?_, ?_⟩
  · have e : ((B.toAf y⁻¹, GlobalTheory.LKCx.toP1 G B.β y⁻¹) : G.GAf × Gr G 1) = (B.toAf y, GlobalTheory.LKCx.toP1 G B.β y)⁻¹ := by
      simp [map_inv]
    have h1 : b.1 = (B.toAf y, GlobalTheory.LKCx.toP1 G B.β y) * a.1 * k := h1
    show a.1 = (B.toAf y⁻¹, GlobalTheory.LKCx.toP1 G B.β y⁻¹) * b.1 * k⁻¹
    rw [e, h1]
    show _ = (B.toAf y, GlobalTheory.LKCx.toP1 G B.β y)⁻¹ * ((B.toAf y, GlobalTheory.LKCx.toP1 G B.β y) * a.1 * k) * k⁻¹
    group
  · rw [h2, Matrix.mulVec_smul, toV_inv', smul_smul, inv_mul_cancel₀ hc, one_smul]

private theorem same_trans' {B : GlobalTheory.LKCx.Form G} {Kf : Subgroup G.GAf} {a b d : GlobalTheory.LKCx.Dat G v B.β}
    (h : SameB v B Kf a b) (h' : SameB v B Kf b d) : SameB v B Kf a d := by
  obtain ⟨y, k, c, hk1, hk2, hc, h1, h2⟩ := h
  obtain ⟨y', k', c', hk1', hk2', hc', h1', h2'⟩ := h'
  refine ⟨y' * y, k * k', c' * c, Kf.mul_mem hk1 hk1', (KHT p G.m G.n 1 G.Fw).mul_mem hk2 hk2',
    mul_ne_zero hc' hc, ?_, ?_⟩
  · have e : ((B.toAf (y' * y), GlobalTheory.LKCx.toP1 G B.β (y' * y)) : G.GAf × Gr G 1) =
        (B.toAf y', GlobalTheory.LKCx.toP1 G B.β y') * (B.toAf y, GlobalTheory.LKCx.toP1 G B.β y) := by
      simp [map_mul]
    show d.1 = (B.toAf (y' * y), GlobalTheory.LKCx.toP1 G B.β (y' * y)) * a.1 * (k * k')
    have h1a : b.1 = (B.toAf y, GlobalTheory.LKCx.toP1 G B.β y) * a.1 * k := h1
    have h1b : d.1 = (B.toAf y', GlobalTheory.LKCx.toP1 G B.β y') * b.1 * k' := h1'
    rw [h1b, h1a, e]
    simp only [_root_.mul_assoc]
  · rw [h2', h2, Matrix.mulVec_smul, smul_smul, toV_mul']

private theorem same_of_eq {B : GlobalTheory.LKCx.Form G} {Kf : Subgroup G.GAf} {a b : GlobalTheory.LKCx.Dat G v B.β}
    (h : Quot.mk (SameB v B Kf) a = Quot.mk (SameB v B Kf) b) : SameB v B Kf a b :=
  (Equivalence.eqvGen_iff ⟨GlobalTheory.LKCx.same_refl G v B.β _ _ _ _ _, same_symm', same_trans'⟩).1 (Quot.eqvGen_exact h)

private theorem step1 {B : GlobalTheory.LKCx.Form G} {K K' : Subgroup G.GAf} (hle : K' ≤ K) {a a' : GlobalTheory.LKCx.Dat G v B.β}
    {k k' : G.GAf} (hk : k ∈ K) (hk' : k' ∈ K) (hs : SameB v B K' (shf a k) (shf a' k')) : SameB v B K a a' := by
  obtain ⟨y, κ, c, h1, h2, hc, e, e2⟩ := hs
  have e1 : a'.1.1 * k' = B.toAf y * (a.1.1 * k) * κ.1 := congrArg Prod.fst e
  have e3 : a'.1.2 = GlobalTheory.LKCx.toP1 G B.β y * a.1.2 * κ.2 := congrArg Prod.snd e
  refine ⟨y, (k * κ.1 * k'⁻¹, κ.2), c, K.mul_mem (K.mul_mem hk (hle h1)) (K.inv_mem hk'), h2, hc, ?_, e2⟩
  refine Prod.ext ?_ e3
  show a'.1.1 = B.toAf y * a.1.1 * (k * κ.1 * k'⁻¹)
  calc a'.1.1 = (a'.1.1 * k') * k'⁻¹ := by group
    _ = _ := by rw [e1]; group

private theorem step2 {B : GlobalTheory.LKCx.Form G} {K K' : Subgroup G.GAf} (hle : K' ≤ K)
    (hK : ∀ (a : GlobalTheory.LKCx.Dat G v B.β) y, W2.Sees B (K : Set G.GAf) a y → y = 1) {a : GlobalTheory.LKCx.Dat G v B.β}
    {k k' : G.GAf} (hk : k ∈ K) (hk' : k' ∈ K) (hs : SameB v B K' (shf a k) (shf a k')) :
    ∃ κ ∈ K', k' = k * κ := by
  obtain ⟨y, κ, c, h1, h2, hc, e, e2⟩ := hs
  have e1 : a.1.1 * k' = B.toAf y * (a.1.1 * k) * κ.1 := congrArg Prod.fst e
  have e3 : a.1.2 = GlobalTheory.LKCx.toP1 G B.β y * a.1.2 * κ.2 := congrArg Prod.snd e
  have e4 : a.2.1 = c • ((GlobalTheory.LKCx.toV G v B.β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a.2.1) := e2
  have hy : y = 1 := by
    refine hK a y ⟨⟨c⁻¹, ?_⟩, ?_, ?_⟩
    · calc (GlobalTheory.LKCx.toV G v B.β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a.2.1
          = c⁻¹ • (c • ((GlobalTheory.LKCx.toV G v B.β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a.2.1)) := by
            rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
        _ = c⁻¹ • a.2.1 := by rw [← e4]
    · have e5 : B.toAf y * a.1.1 = a.1.1 * k' * κ.1⁻¹ * k⁻¹ := by rw [e1]; group
      have e6 : a.1.1⁻¹ * B.toAf y * a.1.1 = k' * κ.1⁻¹ * k⁻¹ := by
        rw [_root_.mul_assoc, e5]; group
      show a.1.1⁻¹ * B.toAf y * a.1.1 ∈ K
      rw [e6]
      exact K.mul_mem (K.mul_mem hk' (K.inv_mem (hle h1))) (K.inv_mem hk)
    · have e5 : GlobalTheory.LKCx.toP1 G B.β y * a.1.2 = a.1.2 * κ.2⁻¹ := by
        conv_rhs => rw [e3]
        group
      have e6 : a.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * a.1.2 = κ.2⁻¹ := by
        rw [_root_.mul_assoc, e5]; group
      rw [e6]
      exact (KHT p G.m G.n 1 G.Fw).inv_mem h2
  subst hy
  rw [map_one, _root_.one_mul, _root_.mul_assoc] at e1
  exact ⟨κ.1, h1, mul_left_cancel e1⟩

private theorem step3 {B : GlobalTheory.LKCx.Form G} {K K' : Subgroup G.GAf} {h : G.GAf} (hle : K' ≤ K)
    (hconj : ∀ u ∈ K', h * u * h⁻¹ ∈ K)
    (hK : ∀ (a : GlobalTheory.LKCx.Dat G v B.β) y, W2.Sees B (K : Set G.GAf) a y → y = 1) {a : GlobalTheory.LKCx.Dat G v B.β}
    {k κ : G.GAf} (hk : k ∈ K) (hκ : κ ∈ K') {y y' : GlobalTheory.LKCx.grp G B.β}
    (hs : W2.Sees B {g | h * g ∈ K} (shf a k) y) (hs' : W2.Sees B {g | h * g ∈ K} (shf a (k * κ)) y') : y = y' := by
  obtain ⟨⟨e, he⟩, h1, h2⟩ := hs
  obtain ⟨⟨e', he'⟩, h1', h2'⟩ := hs'
  have he0 : (GlobalTheory.LKCx.toV G v B.β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a.2.1 = e • a.2.1 := he
  have he1 : (GlobalTheory.LKCx.toV G v B.β y' : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a.2.1 = e' • a.2.1 := he'
  have g1 : h * ((a.1.1 * k)⁻¹ * B.toAf y * (a.1.1 * k)) ∈ K := h1
  have g2 : h * ((a.1.1 * (k * κ))⁻¹ * B.toAf y' * (a.1.1 * (k * κ))) ∈ K := h1'
  have g3 : a.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * a.1.2 ∈ KHT p G.m G.n 1 G.Fw := h2
  have g4 : a.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y' * a.1.2 ∈ KHT p G.m G.n 1 G.Fw := h2'
  have g5 : h * ((a.1.1 * k)⁻¹ * B.toAf y' * (a.1.1 * k)) ∈ K := by
    have := K.mul_mem (K.mul_mem (hconj κ hκ) g2) (K.inv_mem (hle hκ))
    convert this using 1
    group
  have hz : a.2.1 ≠ 0 := by
    intro h0
    have := a.2.2
    rw [h0] at this
    simp at this
  have hinv : e • ((GlobalTheory.LKCx.toV G v B.β y⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a.2.1) = a.2.1 := by
    rw [← Matrix.mulVec_smul, ← he0, toV_inv']
  have he2 : e ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hinv
    exact hz hinv.symm
  have hinv' : (GlobalTheory.LKCx.toV G v B.β y⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a.2.1 = e⁻¹ • a.2.1 := by
    conv_rhs => rw [← hinv]
    rw [smul_smul, inv_mul_cancel₀ he2, one_smul]
  have hone := hK a (y⁻¹ * y') ⟨⟨e' * e⁻¹, ?_⟩, ?_, ?_⟩
  · exact inv_mul_eq_one.1 hone
  · rw [toV_mul', he1, Matrix.mulVec_smul, hinv', smul_smul]
  · show a.1.1⁻¹ * B.toAf (y⁻¹ * y') * a.1.1 ∈ K
    have := K.mul_mem (K.mul_mem hk (K.mul_mem (K.inv_mem g1) g5)) (K.inv_mem hk)
    rw [map_mul, map_inv]
    convert this using 1
    group
  · have := (KHT p G.m G.n 1 G.Fw).mul_mem ((KHT p G.m G.n 1 G.Fw).inv_mem g3) g4
    rw [map_mul, map_inv]
    convert this using 1
    group

end UpperTheory.Gal.FixZ.ComplexFinitenessOfFixed

open UpperTheory.Gal.FixZ.ComplexFinitenessOfFixed in
theorem UpperTheory.Gal.FixZ.cxFinOf_of : UpperTheory.Gal.FixZ.CxFinOf := by
  intro p _ G v K K' h hle hconj hfin hK
  have hS : ∀ u ∈ K', ∀ g, u⁻¹ * g * u ∈ ({g | h * g ∈ K} : Set G.GAf) ↔ g ∈ ({g | h * g ∈ K} : Set G.GAf) := by
    intro u hu g
    constructor
    · intro hg
      have hg' : h * (u⁻¹ * g * u) ∈ K := hg
      have := K.mul_mem (K.mul_mem (hconj u hu) hg') (K.inv_mem (hle hu))
      show h * g ∈ K
      convert this using 1
      group
    · intro hg
      have hg' : h * g ∈ K := hg
      have := K.mul_mem (K.mul_mem (K.inv_mem (hconj u hu)) hg') (hle hu)
      show h * (u⁻¹ * g * u) ∈ K
      convert this using 1
      group
  have hch : ∀ z : (Σ q : GlobalTheory.LKCx.FCls G, UpperTheory.Gal.LocalSmoothExtension.PtsOf G v K q × GlobalTheory.LKCx.grp G (Quot.out q).β),
      UpperTheory.Gal.LocalSmoothExtension.Seen G v K (UpperTheory.Gal.G3.ind ℂ K h⁻¹) z.1 z.2.1 z.2.2 →
      ∃ k, k ∈ K ∧ UpperTheory.Gal.W2.Sees (Quot.out z.1) {g | h * g ∈ K} (shf (Quot.out z.2.1) k) z.2.2 := by
    rintro ⟨q, a, y⟩ ⟨hf, hi, ho⟩
    have hm := Set.mem_of_indicator_ne_zero hi
    obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := DoubleCoset.mem_doubleCoset.1 hm
    refine ⟨k₁, hk₁, hf, ?_, Set.mem_of_indicator_ne_zero ho⟩
    have e' : (Quot.out a).1.1⁻¹ * (Quot.out q).toAf y * (Quot.out a).1.1 = k₁ * h⁻¹ * k₂ := e
    show h * (((Quot.out a).1.1 * k₁)⁻¹ * (Quot.out q).toAf y * ((Quot.out a).1.1 * k₁)) ∈ K
    have e2 : h * (((Quot.out a).1.1 * k₁)⁻¹ * (Quot.out q).toAf y * ((Quot.out a).1.1 * k₁)) =
        h * (k₁⁻¹ * ((Quot.out a).1.1⁻¹ * (Quot.out q).toAf y * (Quot.out a).1.1) * k₁) := by group
    rw [e2, e']
    have e3 : h * (k₁⁻¹ * (k₁ * h⁻¹ * k₂) * k₁) = k₂ * k₁ := by group
    rw [e3]
    exact K.mul_mem hk₂ hk₁
  choose! κ hκK hκS using hch
  refine Set.Finite.of_injOn
    (f := fun z => (⟨z.1, Quot.mk _ (shf (Quot.out z.2.1) (κ z))⟩ : GlobalTheory.LKCx.AllPts G v K' (UpperTheory.Gal.LocalSmoothExtension.Kp G)))
    ?_ ?_ hfin
  · intro z hz
    obtain ⟨E, -, hE⟩ := UpperTheory.Gal.W2.eigSame_of p G v (fun _ _ => 0) (Quot.out z.1) K' {g | h * g ∈ K} hS
      (shf (Quot.out z.2.1) (κ z)) _ (Quot.out_eq _).symm
    exact ⟨E z.2.2, ((hE z.2.2).1).1 (hκS z hz)⟩
  · rintro ⟨q, a, y⟩ hz ⟨q', a', y'⟩ hz' heq
    obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.1 heq
    have hh' := eq_of_heq hh
    have hsame := same_of_eq (v := v) (B := Quot.out q) (Kf := K') hh'
    have hk := hκK _ hz
    have hk' := hκK _ hz'
    have hsame0 := step1 hle hk hk' hsame
    have haa : a = a' := (Quot.out_eq (r := SameB v (Quot.out q) K) a).symm.trans
      ((Quot.sound hsame0).trans (Quot.out_eq (r := SameB v (Quot.out q) K) a'))
    subst haa
    obtain ⟨u, hu, e⟩ := step2 hle (hK _) hk hk' hsame
    have hs := hκS _ hz
    have hs' := hκS _ hz'
    simp only [e] at hs'
    have : y = y' := step3 hle hconj (hK _) hk hu hs hs'
    subst this
    rfl

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PDescEt
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

namespace UpperTheory.Gal.FixZ

theorem descEt_of : DescEt := by
  intro A B C c f hc hs hf hcf
  exact GlobalTheory.etale_of_comp_of_etale_of_surjective c f

end UpperTheory.Gal.FixZ
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PDescFin
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

namespace UpperTheory.Gal.FixZ

theorem descFin_of : DescFin := by
  intro A B C c f hc hs he hfin
  have : UniversallyClosed f := UniversallyClosed.of_comp_surjective c f
  have : IsProper f := { }
  have : LocallyQuasiFinite f := GlobalTheory.TangentCrit.locallyQuasiFinite_of_formallyUnramified f
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end UpperTheory.Gal.FixZ
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PEtCancel
section
open AlgebraicGeometry in
theorem UpperTheory.Gal.FixZ.etCancel_of :
    UpperTheory.Gal.FixZ.EtCancel := by
  intro A B C E f g f' hg hfin1 het1 hfin2 het2
  have h1 : AlgebraicGeometry.IsSeparated (CategoryTheory.CategoryStruct.comp g f') :=
    inferInstance
  have h2 : AlgebraicGeometry.IsSeparated g := AlgebraicGeometry.IsSeparated.of_comp g f'
  have h3 : AlgebraicGeometry.FormallyUnramified g :=
    AlgebraicGeometry.FormallyUnramified.of_comp g f'
  exact ⟨AlgebraicGeometry.IsFinite.of_comp f g, AlgebraicGeometry.Etale.of_comp f g⟩
end

