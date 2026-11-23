module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0038
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFamilyExponentialLocally
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0803

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PHolPi
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem pow_zero_hom_isIso {X : Scheme.{0}} (A : Over X) : IsIso (GlobalTheory.KS.pow A 0).hom := by
  let t : Over.mk (𝟙 X) ⟶ GlobalTheory.KS.pow A 0 := Pi.lift fun i => Fin.elim0 i
  let u : GlobalTheory.KS.pow A 0 ⟶ Over.mk (𝟙 X) := Over.homMk (GlobalTheory.KS.pow A 0).hom
  have h1 : u ≫ t = 𝟙 _ := Pi.hom_ext _ _ fun i => Fin.elim0 i
  refine ⟨⟨t.left, ?_, ?_⟩⟩
  · have h2 := congrArg Over.Hom.left h1
    simpa [u] using h2
  · simpa using Over.w t

private noncomputable def tailMap {X : Scheme.{0}} (A : Over X) (k : ℕ) : GlobalTheory.KS.pow A (k + 1) ⟶ GlobalTheory.KS.pow A k :=
  Pi.lift fun j => GlobalTheory.KS.pr A j.succ

private theorem tailMap_pr {X : Scheme.{0}} (A : Over X) (k : ℕ) (j : Fin k) :
    tailMap A k ≫ GlobalTheory.KS.pr A j = GlobalTheory.KS.pr A j.succ := by
  simp [tailMap, GlobalTheory.KS.pr]

set_option maxHeartbeats 400000 in
private theorem pow_succ_isPullback {X : Scheme.{0}} (A : Over X) (k : ℕ) :
    IsPullback (GlobalTheory.KS.pr A (0 : Fin (k + 1))).left (tailMap A k).left A.hom (GlobalTheory.KS.pow A k).hom := by
  refine Over.isPullback_of_binaryFan_isLimit (BinaryFan.mk (GlobalTheory.KS.pr A (0 : Fin (k + 1))) (tailMap A k)) ?_
  refine BinaryFan.IsLimit.mk _ (fun f g => Pi.lift (Fin.cases f (fun j => g ≫ GlobalTheory.KS.pr A j))) ?_ ?_ ?_
  · intro T f g
    simp [GlobalTheory.KS.pr]
  · intro T f g
    refine Pi.hom_ext _ _ fun j => ?_
    simp [tailMap, GlobalTheory.KS.pr]
  · intro T f g m h1 h2
    simp only [BinaryFan.mk_fst, BinaryFan.mk_snd] at h1 h2
    refine Pi.hom_ext (f := fun _ : Fin (k + 1) => A) (m : T ⟶ ∏ᶜ fun _ : Fin (k + 1) => A) _ fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [← h1, GlobalTheory.KS.pr]
    · rw [← h2]
      simp [tailMap, GlobalTheory.KS.pr]

theorem UpperTheory.Gal.W2.holPi_of :
    UpperTheory.Gal.W2.HolPi := by
  intro V _ _ X A k
  induction k with
  | zero =>
    intro B s hB h0 _
    haveI := pow_zero_hom_isIso A
    refine GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_congr
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp h0 (inv (GlobalTheory.KS.pow A 0).hom)) ?_
    intro b _
    simp
  | succ k ih =>
    intro B s hB h0 hj
    refine GlobalTheory.HolPullback.isHolTo_of_components V B _ _ _ _ _ _ _ _ s (pow_succ_isPullback A k) hB (hj 0) ?_
    apply ih B (fun v => s v ≫ (tailMap A k).left) hB
    · refine GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_congr h0 ?_
      intro b _
      simp only [Category.assoc, Over.w]
    · intro j
      refine GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_congr (hj j.succ) ?_
      intro b _
      simp only [Category.assoc]
      rw [← Over.comp_left, tailMap_pr]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PLocSum
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.locSum_of :
    UpperTheory.Gal.W2.LocTan → UpperTheory.Gal.W2.TorusCount → UpperTheory.Gal.W2.PiLattice → UpperTheory.Gal.W2.PtFibre → UpperTheory.Gal.W2.CorrChart → UpperTheory.Gal.W2.DetOfCharpoly → UpperTheory.Gal.W2.LocSum := by
  intro hTan hCount hPi hFib hChart hDet O _ bar g ρ D X s A _ S d hs k Z sZ c₁ c₂ h₁ h₂ P₀ M₀ hP hM co hco ga H hga T hT L hL hlat hinj hdT hdΘ
  classical
  have hrange : Submodule.span ℝ ((P₀.range : AddSubgroup (Fin g → ℂ)) : Set (Fin g → ℂ)) = ⊤ := by
    rw [AddMonoidHom.coe_range]; exact hP.2.2.2.1
  obtain ⟨hdisc, hspan⟩ := hPi g k P₀.range hP.2.2.1 hrange
  set Λk : AddSubgroup (Fin k → Fin g → ℂ) :=
    AddSubgroup.pi (Set.univ : Set (Fin k)) (fun _ => P₀.range) with hΛk
  have memΛ : ∀ z : Fin k → Fin g → ℂ, z ∈ Λk ↔ ∀ j, z j ∈ P₀.range := by
    intro z; simp [hΛk, AddSubgroup.mem_pi]
  obtain ⟨Fz, hFz1, hFz2, hFzc⟩ := hCount (Fin k → Fin g → ℂ) Λk hdisc hspan (fibMap H L)
    (fun z hz => (memΛ _).2 (hlat z ((memΛ z).1 hz))) hdΘ
  obtain ⟨hf1, hf2, hf3, hf4, hf5⟩ := hFib O bar g ρ D X s A S k P₀ hP
  have e0 : H * 0 * (H.map star)⁻¹ = 0 := by rw [Matrix.mul_zero, Matrix.zero_mul]
  have key : ∀ z, S.pt k P₀ z ≫ c₂ = S.pt k P₀ (fibMap H L z) ≫ c₁ := by
    intro z
    have h := hChart O bar g ρ D X s A S k Z c₁ c₂ P₀ M₀ hP hM ga H hga L hL 0
      (by rw [perC_zero]; exact hP) (by rw [e0, perC_zero]; exact hP) z
    rw [e0, perC_zero] at h
    exact h
  have fixIff : ∀ z, S.pt k P₀ z ≫ c₁ = S.pt k P₀ z ≫ c₂ ↔ fibMap H L z - z ∈ Λk := by
    intro z
    constructor
    · intro h
      have h' : S.pt k P₀ z = S.pt k P₀ (fibMap H L z) := hinj _ _ (h.trans (key z))
      exact (memΛ _).2 ((hf4 _ _).1 h'.symm)
    · intro h
      have h' := (hf4 (fibMap H L z) z).2 ((memΛ _).1 h)
      rw [key z, h']
  let mk : (Fin k → Fin g → ℂ) → CxPts ((GlobalTheory.KS.pow A k).hom ≫ s) (RingHom.id ℂ) :=
    fun z => ⟨S.pt k P₀ z, by rw [← Category.assoc, hf1 z]; exact S.ov P₀ hP⟩
  have mkInj : Set.InjOn mk Fz := by
    intro z hz z' hz' h
    have h1 : S.pt k P₀ z = S.pt k P₀ z' := congrArg Subtype.val h
    have h2 : z - z' ∈ Λk := (memΛ _).2 ((hf4 z z').1 h1)
    obtain ⟨w, _, hw⟩ := hFz2 z (hFz1 z hz)
    have a := hw z ⟨hz, by rw [sub_self]; exact zero_mem _⟩
    have b := hw z' ⟨hz', h2⟩
    exact a.trans b.symm
  refine ⟨Fz.image mk, ?_, ?_⟩
  · intro y
    rw [Finset.mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hf1 z, (fixIff z).2 (hFz1 z hz)⟩
    · rintro ⟨ho, hfx⟩
      obtain ⟨z, hz⟩ := hf3 y.1 ho
      have hz1 : fibMap H L z - z ∈ Λk := (fixIff z).1 (by rw [← hz]; exact hfx)
      obtain ⟨z', ⟨hz'F, hz'⟩, _⟩ := hFz2 z hz1
      refine ⟨z', hz'F, Subtype.ext ?_⟩
      show S.pt k P₀ z' = y.1
      rw [hz]; exact ((hf4 z z').2 ((memΛ _).1 hz')).symm
  · intro At hAt
    have hdet : ∀ y ∈ Fz.image mk, ∀ t : ℂ, (1 - t • At y).det =
        LinearMap.det (1 - t • T) * LinearMap.det (1 - t • fibMap H L) := by
      intro y hy t
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
      have hcp := hTan O bar g ρ D X s A S d hs k Z sZ c₁ c₂ h₁ h₂ P₀ M₀ hP hM co hco ga H hga T hT L hL z
        ((memΛ _).1 (hFz1 z hz)) (mk z) rfl (At (mk z)) (hAt _ hy)
      exact hDet _ _ T (fibMap H L) _ _ hcp t
    have hdet1 : ∀ y ∈ Fz.image mk, (1 - At y).det =
        LinearMap.det (1 - T) * LinearMap.det (1 - fibMap H L) := by
      intro y hy
      have h := hdet y hy 1
      simpa only [one_smul] using h
    refine ⟨fun y hy => by rw [hdet1 y hy]; exact mul_ne_zero hdT hdΘ, fun t => ?_⟩
    have hterm : ∀ y ∈ Fz.image mk, lefTerm (At y) t =
        LinearMap.det (1 - t • T) * LinearMap.det (1 - t • fibMap H L) /
          (LinearMap.det (1 - T) * LinearMap.det (1 - fibMap H L)) := by
      intro y hy
      unfold lefTerm
      rw [hdet y hy t, hdet1 y hy]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_image_of_injOn mkInj, nsmul_eq_mul, hFzc]
    field_simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PLocTan
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem affineMap_hasFDerivAt (hTri : UpperTheory.Gal.W2.TriCharpoly) {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (T : V →ₗ[ℂ] V) (Θ : W →ₗ[ℂ] W) (R : V →ₗ[ℂ] W) (c : V × W) (G : V × W → V × W)
    (hG : ∀ v, G v = (T v.1, Θ v.2 + R v.1) + c) (v₀ : V × W) :
    ∃ G' : (V × W) →L[ℂ] (V × W), HasFDerivAt G G' v₀ ∧
      (G' : (V × W) →ₗ[ℂ] (V × W)).charpoly = T.charpoly * Θ.charpoly := by
  unfold UpperTheory.Gal.W2.TriCharpoly at hTri
  let Gl : (V × W) →ₗ[ℂ] (V × W) :=
    LinearMap.prod (T ∘ₗ LinearMap.fst ℂ V W) (Θ ∘ₗ LinearMap.snd ℂ V W + R ∘ₗ LinearMap.fst ℂ V W)
  let G' : (V × W) →L[ℂ] (V × W) := LinearMap.toContinuousLinearMap Gl
  refine ⟨G', ?_, ?_⟩
  · have hfun : G = fun v => G' v + c := by
      funext v
      rw [hG v]
      rfl
    rw [hfun]
    exact G'.hasFDerivAt.add_const c
  · have hc : (G' : (V × W) →ₗ[ℂ] (V × W)) = Gl := rfl
    rw [hc]
    exact hTri V W T Θ R Gl (fun v w => rfl)

theorem UpperTheory.Gal.W2.locTan_of :
    UpperTheory.Gal.W2.TanChart → UpperTheory.Gal.W2.PerNear → UpperTheory.Gal.W2.BaseImm → UpperTheory.Gal.W2.PtHol → UpperTheory.Gal.W2.PtImm → UpperTheory.Gal.W2.PtFibre → UpperTheory.Gal.W2.CorrChart → UpperTheory.Gal.W2.TriCharpoly → UpperTheory.Gal.W2.LocTan := by
  intro hTan hPer hBase hHol hImm hFib hCorr hTri
  unfold UpperTheory.Gal.W2.TanChart at hTan
  unfold UpperTheory.Gal.W2.PerNear at hPer
  unfold UpperTheory.Gal.W2.BaseImm at hBase
  unfold UpperTheory.Gal.W2.PtHol at hHol
  unfold UpperTheory.Gal.W2.PtImm at hImm
  unfold UpperTheory.Gal.W2.PtFibre at hFib
  unfold UpperTheory.Gal.W2.CorrChart at hCorr
  unfold UpperTheory.Gal.W2.LocTan
  intro O _ bar g ρ D X s A _ S d hsm k Z sZ c₁ c₂ h₁ h₂ P₀ M₀ hP₀ hM co hco ga H hfix T hT L hL z₀ hz₀ y hy At hAt
  have hCsp : ∀ b, co b ∈ Csp bar ρ M₀ := by
    intro b
    have hco' := hco
    unfold IsCoordC at hco'
    rw [← hco'.2]
    exact LinearMap.mem_range_self co b
  obtain ⟨B0, hB0o, h0B0, hB0⟩ := hPer O bar g ρ D P₀ M₀ hP₀ hM d co hCsp
  have hB0' := hB0
  unfold PELU.IsHolPeriods at hB0'
  choose x hx using hz₀
  let sec : (Fin d → ℂ) × (Fin k → Fin g → ℂ) → (Sp ℂ ⟶ (KS.pow A k).left) :=
    fun bz => S.pt k (perC P₀ (co bz.1)) bz.2
  let R : (Fin d → ℂ) →ₗ[ℂ] (Fin k → Fin g → ℂ) :=
    { toFun := fun b j => -(co (T b) *ᵥ star (P₀ (x j)))
      map_add' := by
        intro a b
        funext j
        simp only [map_add (f := _), Matrix.add_mulVec, Pi.add_apply, neg_add]
      map_smul' := by
        intro c b
        funext j
        simp [Matrix.smul_mulVec] }
  let c : (Fin d → ℂ) × (Fin k → Fin g → ℂ) := (0, fun j => -(P₀ (x j)))
  let G : (Fin d → ℂ) × (Fin k → Fin g → ℂ) → (Fin d → ℂ) × (Fin k → Fin g → ℂ) :=
    fun v => (T v.1, fibMap H L v.2 - fun j => perC P₀ (co (T v.1)) (x j))
  have hG : ∀ v, G v = (T v.1, fibMap H L v.2 + R v.1) + c := by
    intro v
    refine Prod.ext ?_ ?_
    · show T v.1 = T v.1 + 0
      rw [add_zero]
    · funext j
      show fibMap H L v.2 j - perC P₀ (co (T v.1)) (x j) =
        fibMap H L v.2 j + -(co (T v.1) *ᵥ star (P₀ (x j))) + -(P₀ (x j))
      rw [perC_apply]
      abel
  obtain ⟨G', hG'd, hG'c⟩ := affineMap_hasFDerivAt hTri T (fibMap H L) R c G hG ((0 : Fin d → ℂ), z₀)
  have hfix0 : G ((0 : Fin d → ℂ), z₀) = ((0 : Fin d → ℂ), z₀) := by
    refine Prod.ext (map_zero T) ?_
    funext j
    show fibMap H L z₀ j - perC P₀ (co (T 0)) (x j) = z₀ j
    rw [map_zero T, map_zero co, perC_zero, hx j, sub_sub_cancel]
  have hsec0 : (y : Sp ℂ ⟶ (KS.pow A k).left) = sec ((0 : Fin d → ℂ), z₀) := by
    show _ = S.pt k (perC P₀ (co 0)) z₀
    rw [map_zero co, perC_zero]
    exact hy
  have hev : ∀ᶠ v in 𝓝 ((0 : Fin d → ℂ), z₀), sec v ≫ c₂ = sec (G v) ≫ c₁ := by
    have hTc : Continuous (fun v : (Fin d → ℂ) × (Fin k → Fin g → ℂ) => T v.1) :=
      (LinearMap.continuous_of_finiteDimensional T).comp continuous_fst
    have hT0 : Filter.Tendsto (fun v : (Fin d → ℂ) × (Fin k → Fin g → ℂ) => T v.1)
        (𝓝 ((0 : Fin d → ℂ), z₀)) (𝓝 0) := by
      have := hTc.tendsto ((0 : Fin d → ℂ), z₀)
      simpa using this
    have h1 : ∀ᶠ v in 𝓝 ((0 : Fin d → ℂ), z₀), v.1 ∈ B0 :=
      (continuous_fst.tendsto ((0 : Fin d → ℂ), z₀)).eventually (hB0o.eventually_mem h0B0)
    have h2 : ∀ᶠ v in 𝓝 ((0 : Fin d → ℂ), z₀), T v.1 ∈ B0 :=
      hT0.eventually (hB0o.eventually_mem h0B0)
    filter_upwards [h1, h2] with v hv1 hv2
    obtain ⟨b, z⟩ := v
    have hPb : PELU.IsPeriod D ρ (perC P₀ (co b)) := hB0'.1 b hv1
    have hPTb : PELU.IsPeriod D ρ (perC P₀ (co (T b))) := hB0'.1 (T b) hv2
    have hPTb' : PELU.IsPeriod D ρ (perC P₀ (H * co b * (H.map star)⁻¹)) := by
      rw [← hT b]
      exact hPTb
    have step := hCorr O bar g ρ D X s A S k Z c₁ c₂ P₀ M₀ hP₀ hM ga H hfix L hL (co b) hPb hPTb' z
    show S.pt k (perC P₀ (co b)) z ≫ c₂ =
      S.pt k (perC P₀ (co (T b))) (fibMap H L z - fun j => perC P₀ (co (T b)) (x j)) ≫ c₁
    rw [step, ← hT b]
    congr 1
    refine ((hFib O bar g ρ D X s A S k _ hPTb).2.2.2.1 _ _).mpr ?_
    intro j
    refine ⟨x j, ?_⟩
    simp [hT b]
  have hflat := hImm O bar g ρ D X s A S k d B0 (fun b => perC P₀ (co b)) 0 hB0o h0B0 hB0
    (hBase O bar g ρ D X s A S d hsm P₀ M₀ hP₀ hM co hco) z₀
  have hhol := hHol O bar g ρ D X s A S k d B0 (fun b => perC P₀ (co b)) hB0o hB0
  have hsecs : ∀ v ∈ B0 ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ)),
      sec v ≫ ((KS.pow A k).hom ≫ s) = spMap (RingHom.id ℂ) := by
    rintro ⟨b, z⟩ ⟨hb, -⟩
    have hPb : PELU.IsPeriod D ρ (perC P₀ (co b)) := hB0'.1 b hb
    show S.pt k (perC P₀ (co b)) z ≫ ((KS.pow A k).hom ≫ s) = _
    rw [← Category.assoc, (hFib O bar g ρ D X s A S k _ hPb).1 z, S.ov _ hPb]
  have hfr : Module.finrank ℂ ((Fin d → ℂ) × (Fin k → Fin g → ℂ)) = d + k * g := by
    simp [Module.finrank_pi_fintype]
  have key := hTan ((Fin d → ℂ) × (Fin k → Fin g → ℂ)) (d + k * g) hfr Z (KS.pow A k).left sZ
    ((KS.pow A k).hom ≫ s) c₁ c₂ h₁ h₂ (B0 ×ˢ Set.univ) sec ((0 : Fin d → ℂ), z₀)
    (hB0o.prod isOpen_univ) ⟨h0B0, trivial⟩ hhol hsecs hflat G G' hG'd hfix0 hev y hsec0 At hAt
  rw [key, hG'c]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPbFlat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem fderiv_line {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (F : V → ℂ) (v₀ w : V)
    (hF : DifferentiableAt ℂ F v₀) :
    DifferentiableAt ℂ (fun z : Fin 1 → ℂ => F (v₀ + z 0 • w)) 0 ∧
      fderiv ℂ (fun z : Fin 1 → ℂ => F (v₀ + z 0 • w)) 0 (fun _ => 1) = fderiv ℂ F v₀ w := by
  have hℓ : HasFDerivAt (fun z : Fin 1 → ℂ => v₀ + z 0 • w)
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).smulRight w) 0 := by
    have h1 : HasFDerivAt (fun z : Fin 1 → ℂ => z 0 • w)
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).smulRight w) 0 :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).smulRight w).hasFDerivAt
    exact h1.const_add v₀
  have hF' : HasFDerivAt F (fderiv ℂ F v₀) ((fun z : Fin 1 → ℂ => v₀ + z 0 • w) 0) := by
    simpa using hF.hasFDerivAt
  have hc : HasFDerivAt (fun z : Fin 1 → ℂ => F (v₀ + z 0 • w))
      ((fderiv ℂ F v₀).comp ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).smulRight w)) 0 :=
    hF'.comp (0 : Fin 1 → ℂ) hℓ
  refine ⟨hc.differentiableAt, ?_⟩
  rw [hc.fderiv]
  simp

private theorem exists_isDerivAt0_line_of_isHolTo {X : Scheme.{0}} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {B : Set V} {t : V → (Sp ℂ ⟶ X)} (ht : IsHolTo B t) {v₀ : V} (hv : v₀ ∈ B) (w : V) :
    ∃ x, IsDerivAt0 (fun z : Fin 1 → ℂ => t (v₀ + z 0 • w)) (fun _ => 1) x := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ ((t v₀) default)) isOpen_univ
  have hW0 : ⊤ ≤ t v₀ ⁻¹ᵁ W := by
    rw [top_le_preimage_iff_mem]
    have hd : (@default (PrimeSpectrum ℂ) _) = (@default (↥(Sp ℂ)) _) := Subsingleton.elim _ _
    rw [hd]
    exact hxW
  have hℓc : Continuous (fun z : Fin 1 → ℂ => v₀ + z 0 • w) := by
    fun_prop
  have hℓ0 : (fun z : Fin 1 → ℂ => v₀ + z 0 • w) 0 = v₀ := by
    simp
  have hev : ∀ᶠ z in 𝓝 (0 : Fin 1 → ℂ), ⊤ ≤ t (v₀ + z 0 • w) ⁻¹ᵁ W := by
    have h1 := LocalLift.hol_eventually_mem ht hv hW0
    have h2 : Tendsto (fun z : Fin 1 → ℂ => v₀ + z 0 • w) (𝓝 0) (𝓝 v₀) := by
      have := hℓc.tendsto 0
      simpa using this
    exact (h2.eventually h1).mono (fun z hz => hz.2)
  have hdiff : ∀ a : Γ(X, W), DifferentiableAt ℂ (fun z : Fin 1 → ℂ => valAt' (t (v₀ + z 0 • w)) W a) 0 :=
    fun a => (fderiv_line (fun v => valAt' (t v) W a) v₀ w
      (LocalLift.hol_differentiableAt ht hv hW0 a)).1
  let ψ : Γ(X, W) →+* DualNumber ℂ :=
    { toFun := fun a => FibreDeriv.jet (fun _ => 1) (fun z : Fin 1 → ℂ => valAt' (t (v₀ + z 0 • w)) W a)
      map_one' := by
        have hc : (fun z : Fin 1 → ℂ => valAt' (t (v₀ + z 0 • w)) W 1) =ᶠ[𝓝 0] (fun _ => (1 : ℂ)) :=
          hev.mono (fun z hz => valAt'_one _ hz)
        rw [FibreDeriv.jet_congr _ hc, FibreDeriv.jet_const]
        simp
      map_mul' := by
        intro a b
        simp only [valAt'_mul]
        exact FibreDeriv.jet_mul _ (hdiff a) (hdiff b)
      map_zero' := by
        simp only [valAt'_zero]
        rw [FibreDeriv.jet_const]
        simp
      map_add' := by
        intro a b
        simp only [valAt'_add]
        exact FibreDeriv.jet_add _ (hdiff a) (hdiff b) }
  obtain ⟨x, hx, hxψ⟩ := TangentOrigin.exists_evalPt_eq hW ψ
  refine ⟨x, FibreDeriv.isDerivAt0_of_affine ?_ hW hx (fun a => ⟨hdiff a, ?_⟩)⟩
  · have h' : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ x) ⁻¹ᵁ W :=
      (TangentOrigin.top_le_preimage_iff x W).mp hx
    have h0 : ⊤ ≤ t (v₀ + (0 : Fin 1 → ℂ) 0 • w) ⁻¹ᵁ W := by
      simpa using hW0
    refine TangentOrigin.ext_evalPt hW h' h0 (RingHom.ext (fun a => ?_))
    rw [TangentOrigin.evalPt_spMap_comp _ x W hx h' a, hxψ, ← TangentOrigin.valAt'_eq_evalPt]
    exact FibreDeriv.fst_jet (fun _ => 1) (fun z : Fin 1 → ℂ => valAt' (t (v₀ + z 0 • w)) W a)
  · show TangentOrigin.evalPt x W hx a = _
    rw [hxψ]
    rfl

private theorem isDerivAt0_line_const_of_flat {X : Scheme.{0}} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {B : Set V} {t : V → (Sp ℂ ⟶ X)} (ht : IsHolTo B t) {v₀ : V} (hv : v₀ ∈ B) (w : V)
    (hf : Flat t v₀ w) :
    IsDerivAt0 (fun z : Fin 1 → ℂ => t (v₀ + z 0 • w)) (fun _ => 1)
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ t v₀) := by
  have h := LocalLift.isDerivAt0_const (fun z : Fin 1 → ℂ => t (v₀ + z 0 • w)) (fun _ => 1)
    (fun U f hU => by
      have hU' : ⊤ ≤ t v₀ ⁻¹ᵁ U := by
        simpa using hU
      rw [(fderiv_line (fun v => valAt' (t v) U f) v₀ w
        (LocalLift.hol_differentiableAt ht hv hU' f)).2]
      exact hf U f hU')
  simpa using h

private theorem flat_of_isDerivAt0_line_const {X : Scheme.{0}} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {B : Set V} {t : V → (Sp ℂ ⟶ X)} (ht : IsHolTo B t) {v₀ : V} (hv : v₀ ∈ B) (w : V)
    (hd : IsDerivAt0 (fun z : Fin 1 → ℂ => t (v₀ + z 0 • w)) (fun _ => 1)
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ t v₀)) :
    Flat t v₀ w := by
  intro U f hU
  rw [← (fderiv_line (fun v => valAt' (t v) U f) v₀ w
    (LocalLift.hol_differentiableAt ht hv hU f)).2]
  have hc : IsDerivAt0 (fun _ : Fin 1 → ℂ => t v₀) (fun _ => 1)
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ t v₀) :=
    LocalLift.isDerivAt0_const (fun _ : Fin 1 → ℂ => t v₀) (fun _ => 1)
      (fun U' f' _ => by simp)
  have h : ⊤ ≤ (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ t v₀) ⁻¹ᵁ U := by
    rw [TangentOrigin.top_le_preimage_iff, hc.1]
    exact hU
  rw [← hd.2 U h f, hc.2 U h f]
  simp

theorem UpperTheory.Gal.W2.pbFlat_of :
    UpperTheory.Gal.W2.FlatAffine → UpperTheory.Gal.W2.PbFlat := by
  intro hFA V _ _ P Y₁ Y₂ T p₁ p₂ f₁ f₂ hpb B s v₀ w hB hv h1 h2 hf1 hf2
  have hs : IsHolTo B s :=
    HolPullback.isHolTo_of_components V B Y₁ P T Y₂ p₁ p₂ f₁ f₂ s hpb hB h1 h2
  obtain ⟨x, hx⟩ := exists_isDerivAt0_line_of_isHolTo hs hv w
  have hc1 := isDerivAt0_line_const_of_flat h1 hv w hf1
  have hc2 := isDerivAt0_line_const_of_flat h2 hv w hf2
  have hx1 := FibreDeriv.isDerivAt0_comp hx p₁
  have hx2 := FibreDeriv.isDerivAt0_comp hx p₂
  have he1 : x ≫ p₁ = (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ s v₀) ≫ p₁ := by
    rw [Category.assoc]
    exact VerticalDeriv.isDerivAt0_unique hx1 hc1
  have he2 : x ≫ p₂ = (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ s v₀) ≫ p₂ := by
    rw [Category.assoc]
    exact VerticalDeriv.isDerivAt0_unique hx2 hc2
  have hxe : x = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ s v₀ := hpb.hom_ext he1 he2
  rw [hxe] at hx
  exact flat_of_isDerivAt0_line_const hs hv w hx
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPerLin
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.perLin_of :
    UpperTheory.Gal.W2.PerLin := by
  intro O _ bar g ρ D P P' H hP hH hc hP'
  have hdet : LinearMap.det (Matrix.toLin' H) ≠ 0 := by rwa [LinearMap.det_toLin']
  let h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearMap.equivOfDetNeZero _ hdet
  have happ : ∀ z, h z = H *ᵥ z := fun z => rfl
  have key := IsPeriod.comp_linearEquiv O bar D g ρ ρ P h hP (fun a z => by
    rw [happ, happ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hc])
  have hEq : P' = (↑h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).toAddMonoidHom.comp P := by
    ext x
    simp [hP', happ]
  rw [hEq]
  exact key
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPiLattice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.piLattice_of :
    UpperTheory.Gal.W2.PiLattice := by
  intro g k Λ hd hs
  constructor
  · let φ : ↥(AddSubgroup.pi Set.univ fun _ : Fin k => Λ) → (Fin k → ↥Λ) :=
      fun x i => ⟨x.1 i, (AddSubgroup.mem_pi _).mp x.2 i trivial⟩
    refine DiscreteTopology.of_continuous_injective (f := φ) ?_ ?_
    · refine continuous_pi fun i => ?_
      exact ((continuous_apply i).comp continuous_subtype_val).subtype_mk _
    · intro x y hxy
      apply Subtype.ext
      funext i
      have := congrArg (fun z => (z i : Fin g → ℂ)) hxy
      simpa [φ] using this
  · rw [eq_top_iff]
    intro w _
    rw [← Finset.univ_sum_single w]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hw : w i ∈ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) := by rw [hs]; trivial
    have hmap : (Submodule.span ℝ (Λ : Set (Fin g → ℂ))).map
        (LinearMap.single ℝ (fun _ : Fin k => Fin g → ℂ) i) ≤
        Submodule.span ℝ ↑(AddSubgroup.pi Set.univ fun _ : Fin k => Λ) := by
      rw [Submodule.map_span]
      apply Submodule.span_mono
      rintro _ ⟨v, hv, rfl⟩
      simp only [SetLike.mem_coe, AddSubgroup.mem_pi]
      intro j _
      by_cases hj : j = i
      · subst hj; simpa using hv
      · simp [hj]
    exact hmap ⟨w i, hw, rfl⟩
end

