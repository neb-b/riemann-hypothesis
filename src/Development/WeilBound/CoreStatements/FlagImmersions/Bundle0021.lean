module

public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle0013
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle0012
public import Development.WeilBound.CoreStatements.VolumeEquality.Pieces
public import Development.WeilBound.CoreStatements.FlagImmersions.Transport
public import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnif
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugateUniversalFamily
public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0004
public import Development.WeilBound.CoreStatements.VolumeEquality.ChartMeetsForm
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0014

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.AnalyticAtAeval
section
noncomputable section

namespace RootFieldNumerics

open AlgebraicGeometry CategoryTheory NumberField Filter Topology MvPolynomial
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB Bh

theorem Bh.analyticAt_aeval {σ : Type} {n : ℕ} {f : σ → (Fin n → ℂ) → ℂ} {t : Fin n → ℂ} (h : ∀ q, AnalyticAt ℂ (f q) t)
    (p : MvPolynomial σ ℤ) : AnalyticAt ℂ (fun u => aeval (fun q => f q u) p) t := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq => simpa using hp.fun_add hq
  | mul_X p i hp => simpa using hp.fun_mul (h i)

theorem biholo_of : Descend → Biholo := by
  intro hD E _ _ _ H D l Xo c Y S RM Sys Fx Or hJ hdeg hamp
  classical
  obtain ⟨m, n, s, hs, hamp⟩ := hamp
  have hd : IsDegreeOff Sys.A Or.Re.R.A Or.Re.π 1 Or.Re.br := by
    have := Or.Re.degree
    rwa [Or.Re_deg, hdeg] at this
  have hsurj := surj_of_degree Or.Re.holo.1 hd
  set R := Or.Re.R with hR
  set π := Or.Re.π with hπ
  let k₀ := Or.k₀
  have hmem : ∀ w, ∀ w' ∈ R.U w, R.lift w w' ∈ mcPts (mCoordIdeal RM.y) := R.mem
  choose z hz using fun w => SheetDecomposition.exists_pt Or.𝔐 (hmem w w (R.mem_U w))
  have hz' : ∀ w, ∀ w' ∈ R.U w, CoordsAt Or.𝔐.ξ RM.y (z w') (R.lift w w') := fun w w' h => by
    obtain ⟨a, ha, e⟩ := R.compat w w' w' ⟨h, R.mem_U w'⟩
    exact SheetDecomposition.coords_of_sat Or.𝔐 (hz w') ⟨_, rfl, a, ha, e⟩
  have hpoly : ∀ i (cc : (k : RM.K) → RM.ι k), (∀ k, RM.y ⟨k, cc k⟩ ≠ 0) → ∃ p : MRing RM.ι,
      aeval (fun q : Σ k, RM.ι k => RM.y q / RM.y ⟨q.1, cc q.1⟩) p = s i * ∏ k, RM.y ⟨k, cc k⟩ ^ (-((m : ℤ) * RM.A.a k - 1)) ∧
      aeval (fun q : Σ k, RM.ι k => RM.y q / RM.y ⟨q.1, cc q.1⟩) p = fn RM.y (s i) m k₀ (cc k₀) cc := fun i cc hc => by
    have h1 := hs i cc hc
    simp only [Nat.cast_one, one_mul] at h1
    obtain ⟨p, hp⟩ := exists_poly Or.𝔐.tie Or.𝔐.normal cc hc h1
    exact ⟨p, hp, hp.trans (fn_eq Or.A_deg cc hc)⟩
  have hchart : ∀ w, ∃ cc : (k : RM.K) → RM.ι k, (∀ k, R.lift w w ⟨k, cc k⟩ ≠ 0) ∧ ∀ k, RM.y ⟨k, cc k⟩ ≠ 0 := fun w => by
    choose cc hc using (hmem w w (R.mem_U w)).1
    exact ⟨cc, hc, fun k => ((hz w).2 k (cc k) (IsUnit.mk0 _ (hc k))).1⟩
  let f : Fin n → RM.ι k₀ → ((k : RM.K) → RM.ι k) → R.X → ℂ := fun i i₀ cc w =>
    if h : ∃ r, ValAt Or.𝔐.ξ (z w) (fn RM.y (s i) m k₀ i₀ cc) r then h.choose else 0
  have hf : ∀ i i₀ cc w r, ValAt Or.𝔐.ξ (z w) (fn RM.y (s i) m k₀ i₀ cc) r → f i i₀ cc w = r := fun i i₀ cc w r h => by
    have h' : ∃ r, ValAt Or.𝔐.ξ (z w) (fn RM.y (s i) m k₀ i₀ cc) r := ⟨r, h⟩
    simp only [f, dif_pos h']
    exact CxVal.unique h'.choose_spec h
  let U : RM.ι k₀ → Set Sys.X := fun i₀ => {x | Fx.pt x (Or.ix.symm i₀) ≠ 0}
  have hU : ∀ i₀ w, π w ∈ U i₀ ↔ R.lift w w ⟨k₀, i₀⟩ ≠ 0 := fun i₀ w => by
    obtain ⟨a, ha⟩ := Or.π_pt w
    have h1 : R.lift w w ⟨k₀, i₀⟩ = a * Fx.pt (π w) (Or.ix.symm i₀) := by
      have := congrFun ha (Or.ix.symm i₀)
      simpa using this
    have h2 : a ≠ 0 := by
      rintro rfl
      obtain ⟨i, hi⟩ := (hmem w w (R.mem_U w)).1 k₀
      have := congrFun ha (Or.ix.symm i)
      exact hi (by simpa using this)
    rw [h1]
    simp [U, h2]
  have hUo : ∀ i₀, IsOpen (U i₀) := fun i₀ => by
    have e : (U i₀)ᶜ = π '' {w | R.lift w w ⟨k₀, i₀⟩ ≠ 0}ᶜ := by
      ext x
      obtain ⟨w, rfl⟩ := hsurj x
      exact ⟨fun h => ⟨w, fun h' => h ((hU _ _).2 h'), rfl⟩, fun ⟨w', h, e⟩ h' => h ((hU _ _).1 (e ▸ h'))⟩
    rw [← isClosed_compl_iff, e]
    exact Or.Re.holo.1.isClosedMap _ (isOpen_lift_ne R _).isClosed_compl
  have hhol : ∀ i i₀ cc, R.A.HoloOn (π ⁻¹' U i₀) (f i i₀ cc) := fun i i₀ cc j t ht => by
    obtain ⟨c', hc', hy'⟩ := hchart ((R.A.chart j).symm t)
    obtain ⟨p, -, hp⟩ := hpoly i c' hy'
    have h0 := (hU _ _).1 ht.2
    set w₁ := (R.A.chart j).symm t with hw₁
    have ha : ∀ q, AnalyticAt ℂ (fun u => R.lift w₁ ((R.A.chart j).symm u) q) t := fun q =>
      R.holo w₁ q j t ⟨ht.1, R.mem_U w₁⟩
    have hA : AnalyticAt ℂ (fun u => aeval (fun q : Σ k, RM.ι k => R.lift w₁ ((R.A.chart j).symm u) q /
        R.lift w₁ ((R.A.chart j).symm u) ⟨q.1, c' q.1⟩) p *
        (∏ k, R.lift w₁ ((R.A.chart j).symm u) ⟨k, cc k⟩ / R.lift w₁ ((R.A.chart j).symm u) ⟨k, c' k⟩) *
        (R.lift w₁ ((R.A.chart j).symm u) ⟨k₀, c' k₀⟩ / R.lift w₁ ((R.A.chart j).symm u) ⟨k₀, i₀⟩) ^ m) t :=
      ((Bh.analyticAt_aeval (fun q => (ha q).fun_div (ha _) (hc' _)) p).fun_mul
        (Finset.analyticAt_fun_prod _ fun k _ => (ha _).fun_div (ha _) (hc' _))).fun_mul
        (((ha _).fun_div (ha _) h0).fun_pow m)
    refine hA.congr ?_
    have e1 : ∀ᶠ u in 𝓝 t, (R.A.chart j).symm u ∈ R.U w₁ :=
      ((R.A.chart j).continuousAt_symm ht.1).eventually_mem ((R.isOpen_U w₁).mem_nhds (R.mem_U w₁))
    have e2 : ∀ᶠ u in 𝓝 t, ∀ k, R.lift w₁ ((R.A.chart j).symm u) ⟨k, c' k⟩ ≠ 0 :=
      Filter.eventually_all.2 fun k => (ha _).continuousAt.eventually_ne (hc' k)
    filter_upwards [e1, e2, (ha _).continuousAt.eventually_ne h0] with u h1 h2 h3
    exact (hf _ _ _ _ _ (val_fn (Or.𝔐.all _) (hz' w₁ _ h1) i₀ cc c' h2 h3 hp)).symm
  choose F hF hFf using fun i i₀ cc =>
    hD _ Sys.X R.X Sys.A R.A π Or.Re.br (U i₀) (f i i₀ cc) Or.Re.holo hd (hUo i₀) (hhol i i₀ cc)
  refine exists_inverse R hJ Sys.A π hsurj fun w₁ => ?_
  obtain ⟨c', hc', hy'⟩ := hchart w₁
  obtain ⟨i, v, hv, hval⟩ := hamp ℂ (R.lift w₁ w₁) ⟨(hmem w₁ w₁ (R.mem_U w₁)).1, fun g hg => by
    have := (hmem w₁ w₁ (R.mem_U w₁)).2 g hg
    rwa [MvPolynomial.eval_map] at this⟩
  obtain ⟨p, hp1, hp2⟩ := hpoly i c' hy'
  have hu := ne_zero_of_hasVal (Or.𝔐.all _) (hz w₁) c' hc' hp1 hv hval
  have hin : π w₁ ∈ U (c' k₀) := (hU _ _).2 (hc' k₀)
  refine ⟨{x ∈ U (c' k₀) | F i (c' k₀) c' x ≠ 0}, fun x q => F i (c' k₀) (Function.update c' q.1 q.2) x, ?_, ⟨hin, ?_⟩,
    fun q j => (hF _ _ _ j).mono fun t ht => ⟨ht.1, ht.2.1⟩, fun w hw => ?_⟩
  · refine isOpen_iff_mem_nhds.2 fun x hx => ?_
    filter_upwards [(hUo _).mem_nhds hx.1, (contAt_of_holoOn (hF i _ c') hx.1).eventually_ne hx.2] with x' h1 h2
    exact ⟨h1, h2⟩
  · rw [hFf _ _ _ _ hin, hf _ _ _ _ _ (val_fn (Or.𝔐.all _) (hz w₁) (c' k₀) c' c' hc' (hc' k₀) hp2)]
    exact mul_ne_zero (mul_ne_zero hu (Finset.prod_ne_zero_iff.2 fun k _ => div_ne_zero (hc' k) (hc' k)))
      (pow_ne_zero _ (div_ne_zero (hc' _) (hc' _)))
  · obtain ⟨c₂, hc₂, hy₂⟩ := hchart w
    obtain ⟨p₂, -, hp₂⟩ := hpoly i c₂ hy₂
    have h0 := (hU _ _).1 hw.1
    obtain ⟨κ, hκ⟩ : ∃ κ : ℂ, ∀ cc, F i (c' k₀) cc (π w) = κ * ∏ k, R.lift w w ⟨k, cc k⟩ := by
      refine ⟨aeval (fun q : Σ k, RM.ι k => R.lift w w q / R.lift w w ⟨q.1, c₂ q.1⟩) p₂ *
        (R.lift w w ⟨k₀, c₂ k₀⟩ / R.lift w w ⟨k₀, c' k₀⟩) ^ m / ∏ k, R.lift w w ⟨k, c₂ k⟩, fun cc => ?_⟩
      rw [hFf _ _ _ _ hw.1, hf _ _ _ _ _ (val_fn (Or.𝔐.all _) (hz w) (c' k₀) cc c₂ hc₂ h0 hp₂), Finset.prod_div_distrib]
      ring
    have h1 := hw.2
    rw [hκ] at h1
    have h2 := left_ne_zero_of_mul h1
    have h3 := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul h1)
    refine SO_symm ⟨fun k => κ * ∏ k' ∈ Finset.univ.erase k, R.lift w w ⟨k', c' k'⟩,
      fun k => mul_ne_zero h2 (Finset.prod_ne_zero_iff.2 fun k' _ => h3 k' (Finset.mem_univ _)), funext fun q => ?_⟩
    obtain ⟨k, j⟩ := q
    show F i (c' k₀) (Function.update c' k j) (π w) = _
    rw [hκ, ← Finset.prod_erase_mul _ _ (Finset.mem_univ k), Function.update_self, mul_assoc]
    congr 2
    exact Finset.prod_congr rfl fun k' hk' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk')]

end RootFieldNumerics
end
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.HasPerConj
section
noncomputable section

namespace RootFieldNumerics

open AlgebraicGeometry CategoryTheory Limits NumberField Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp SheetDecomposition

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K]
  {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)

def HasPer {n : ℕ} (V : Set (Fin n → ℂ)) (z : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)) (t₀ : Fin n → ℂ) : Prop :=
  ∃ (g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (R : (Fin n → ℂ) → RiemLat E g Λ) (V' : Set (Fin n → ℂ)),
    IsOpen V' ∧ t₀ ∈ V' ∧ V' ⊆ V ∧ IsHolFam V' R ∧ VecAt 𝔐 R z t₀

theorem hasPer_good {g : ℕ} (κ : c.F →+* ℂ) (ty : Fin g → (E →+* ℂ)) (hty : IsTypeFn H D.p D.q ty)
    (FU : FamilyUnif Xo (κ.comp (IntermediateField.inclusion c.le).toRingHom) ty) {n : ℕ} {V : Set (Fin n → ℂ)}
    {z : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)} (hV : IsOpen V) (hz : IsHolTo V z) (hi : ∀ t ∈ V, 𝔐.Interior (z t))
    (hs : ∀ t ∈ V, (z t ≫ 𝔐.f) ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F))) {t₀ : Fin n → ℂ} (ht₀ : t₀ ∈ V) :
    HasPer 𝔐 V z t₀ := by
  classical
  have hx : ∀ a, ∃ x : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.snd _ _ = spMap κ ∧ (a ∈ V → x ≫ Y.j = z a ≫ 𝔐.f) := fun a => by
    by_cases ha : a ∈ V
    · obtain ⟨x, h₁, h₂⟩ := exists_j Y κ _ ((interior_iff 𝔐 _).2 (hi a ha)) (hs a ha)
      exact ⟨x, h₂, fun _ => h₁⟩
    · obtain ⟨x, -, h₂⟩ := exists_j Y κ _ ((interior_iff 𝔐 _).2 (hi t₀ ht₀)) (hs t₀ ht₀)
      exact ⟨x, h₂, fun h => absurd h ha⟩
  choose x hxs hxj using hx
  have hol := isHolTo_of_j Y κ hV hxs (GlobalTheory.HolPeriods.isHolTo_congr (PullbackSections.isHolTo_comp hz 𝔐.f) hxj)
  obtain ⟨V', i, P, hV', hm, hsub, hP, hu⟩ := FU.lift n V (fun a => x a ≫ pullback.fst _ _) hV
    (fun a _ => by rw [Category.assoc, pullback.condition, ← Category.assoc, hxs, spMap_comp]) (PullbackSections.isHolTo_comp hol _) t₀ ht₀
  have htyi : IsTypeFn H (FU.Di i).p (FU.Di i).q ty := by
    rw [(FU.sig i).1, (FU.sig i).2]
    exact hty
  have hR : ∀ t, ∃ R : RiemLat E g (FU.Di i).La, R.form = (FU.Di i).EF ∧ (t ∈ V' → R.P = P t) := fun t => by
    by_cases ht : t ∈ V'
    · obtain ⟨R, h₁, h₂, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.riemLat_of_period E H (FU.Di i) g ty _ htyi (hP.1 t ht)
      exact ⟨R, h₂, fun _ => h₁⟩
    · obtain ⟨R, -, h₂, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.riemLat_of_period E H (FU.Di i) g ty _ htyi (hP.1 t₀ hm)
      exact ⟨R, h₂, fun h => absurd h ht⟩
  choose R hf hRP using hR
  refine ⟨g, _, inferInstance, inferInstance, R, V', hV', hm, hsub,
    ⟨fun t _ t' _ => (hf t).trans (hf t').symm, fun a => (hP.2 a).congr fun t ht => by rw [hRP t ht]⟩, ?_⟩
  refine vecOfPeriods_of holCoord E H D l Xo c Y S Ω K J y 𝔐 κ _ g ty FU i n V' z x R P (fun _ => 1) hV'
    (vecMono hz hV' hsub) (vecMono hol hV' hsub) hP (fun _ _ => differentiableOn_const _) (fun t ht => ?_) t₀ hm
  exact ⟨hf t, by simp, fun a => by rw [hRP t ht, Matrix.one_mulVec], hxj t (hsub ht), (hu t ht).symm, hxs t⟩

theorem hasPer_conj {n : ℕ} {V : Set (Fin n → ℂ)} {z : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)} {t₀ : Fin n → ℂ}
    (h : HasPer 𝔐 (star ⁻¹' V) (fun t => spMap (starRingEnd ℂ) ≫ z (star t)) (star t₀)) : HasPer 𝔐 V z t₀ := by
  obtain ⟨g, Λ, _, _, R, V', hV', hm, hsub, hR, hv⟩ := h
  refine ⟨g, Λ, inferInstance, inferInstance, fun t => GlobalTheory.CompanionTheory.Ar.Cusp.ConjFam.conjLat (R (star t)), star ⁻¹' V', hV'.preimage continuous_star, hm,
    fun t ht => by simpa using hsub ht, ⟨fun t ht t' ht' => ?_, fun a => ?_⟩, ?_⟩
  · show -(R (star t)).form = -(R (star t')).form
    rw [hR.1 _ ht _ ht']
  · exact GlobalTheory.CompanionTheory.Ar.Cusp.ConjFam.differentiableOn_conj (hR.2 a) fun t ht => ht
  · exact vecAt_conj 𝔐 R _ z t₀ (fun t => ⟨fun _ => rfl, rfl, fun _ _ => rfl⟩) hv

theorem locPer : LocPer := by
  intro hG E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 n V z h1 hV hz hi t₀ ht₀
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  obtain ⟨ε, hε, hB⟩ := Metric.isOpen_iff.1 hV t₀ ht₀
  have hBo : IsOpen (Metric.ball t₀ ε) := Metric.isOpen_ball
  have hz' := vecMono hz hBo hB
  have hemb : ∀ p : Sp ℂ ⟶ Y.X, ∃ κ : c.F →+* ℂ, p ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F)) := fun p => by
    obtain ⟨κ, hκρ⟩ := FamEx.exists_ringHom_extend (Spec.preimage (p ≫ Y.s)).hom
    refine ⟨κ, ?_⟩
    rw [hκρ]
    unfold spMap
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  choose κ hκy using fun b => hemb (z b ≫ 𝔐.f)
  have hd : ∀ r : 𝓞 c.F, DifferentiableOn ℂ (fun b => κ b (r : c.F)) (Metric.ball t₀ ε) := fun r => by
    have h3 := (PullbackSections.isHolTo_comp (PullbackSections.isHolTo_comp hz' 𝔐.f) Y.s ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 c.F))).inv r)).2
    have hset : Metric.ball t₀ ε ⊆ {b ∈ Metric.ball t₀ ε | ⊤ ≤ ((z b ≫ 𝔐.f) ≫ Y.s) ⁻¹ᵁ ⊤} := fun b hb => ⟨hb, le_top⟩
    refine (h3.mono hset).congr fun b _ => ?_
    show κ b (r : c.F) = valAt' ((z b ≫ 𝔐.f) ≫ Y.s) ⊤ _
    rw [hκy b]
    exact (PullbackSections.valAt'_spMap ((κ b).comp (algebraMap (𝓞 c.F) c.F)) r).symm
  have h0 : t₀ ∈ Metric.ball t₀ ε := Metric.mem_ball_self hε
  have hc : ∀ b ∈ Metric.ball t₀ ε, (z b ≫ 𝔐.f) ≫ Y.s = spMap ((κ t₀).comp (algebraMap (𝓞 c.F) c.F)) := fun b hb => by
    rw [hκy, FamEx.embedding_const_preconnected (convex_ball t₀ ε).isPreconnected κ hd hb h0]
  have hi' : ∀ t ∈ Metric.ball t₀ ε, 𝔐.Interior (z t) := fun t ht => hi t (hB ht)
  have hN : N1c := hG.1.2.2.1
  obtain ⟨g, ty, hty⟩ := GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q
  let ρ : c.F := (IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ
  have key : HasPer 𝔐 (Metric.ball t₀ ε) z t₀ := by
    have e : ρ ^ 2 = -(H.d : c.F) := Subtype.ext (by show (ρ : ℂ) ^ 2 = -(H.d : ℂ); exact H.sqrt_neg_disc_sq)
    have e2 : (κ t₀ ρ) ^ 2 = H.rt0 ^ 2 := by
      rw [← map_pow, e, H.sqrt_neg_disc_sq]
      simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 e2 with h | h
    · obtain ⟨FU⟩ := hN E H D l Xo ((κ t₀).comp (IntermediateField.inclusion c.le).toRingHom) g ty h1 h hty
      exact hasPer_good 𝔐 _ ty hty FU hBo hz' hi' hc h0
    · obtain ⟨FU⟩ := hN E H D l Xo (((starRingEnd ℂ).comp (κ t₀)).comp (IntermediateField.inclusion c.le).toRingHom) g ty h1
        (by
          show starRingEnd ℂ (κ t₀ ρ) = _
          rw [h, map_neg, FamEx.rt0_conj_neg_ne_zero, neg_neg]) hty
      have hs : spMap (((starRingEnd ℂ).comp (κ t₀)).comp (algebraMap (𝓞 c.F) c.F)) =
          spMap (starRingEnd ℂ) ≫ spMap ((κ t₀).comp (algebraMap (𝓞 c.F) c.F)) :=
        Spec.map_comp (CommRingCat.ofHom ((κ t₀).comp (algebraMap (𝓞 c.F) c.F))) (CommRingCat.ofHom (starRingEnd ℂ))
      refine hasPer_conj 𝔐 (hasPer_good 𝔐 _ ty hty FU (hBo.preimage continuous_star) (GlobalTheory.T.holomorphic_family_conjugate _ _ _ _ hz')
        (fun t ht => ?_) (fun t ht => ?_) (by simpa using hε))
      · have h := hi' _ ht
        unfold HodgeCpt.Interior at h ⊢
        rwa [Cj.centre_conj]
      · rw [hs, ← hc _ ht]
        simp only [Category.assoc]
  obtain ⟨g, Λ, i₁, i₂, R, V', hV', hm, hsub, hR, hv⟩ := key
  refine ⟨g, Λ, i₁, i₂, R, V', fun s => (κ t₀).comp (labelEmb c s), hV', hm, hsub.trans hB, hR, fun t ht s => ?_, hv⟩
  have h := hc t (hsub ht)
  rw [Category.assoc] at h
  cases s with
  | inl τ => exact labVal_of_over 𝔐 (hi' t (hsub ht)) h Sum.inl τ
  | inr τ => exact labVal_of_over 𝔐 (hi' t (hsub ht)) h Sum.inr τ

end RootFieldNumerics
end
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.IsHolToOfLocal
section
noncomputable section

namespace RootFieldNumerics

open AlgebraicGeometry CategoryTheory NumberField Filter Topology Matrix
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.PB

namespace Pts

theorem isHolTo_of_local {X : Scheme.{0}} {n : ℕ} {T : Set (Fin n → ℂ)} {y : (Fin n → ℂ) → (Sp ℂ ⟶ X)}
    (h : ∀ t ∈ T, ∃ B, B ⊆ T ∧ t ∈ B ∧ IsHolTo B y) : IsHolTo T y := by
  intro U f
  have key : ∀ t ∈ {b ∈ T | ⊤ ≤ y b ⁻¹ᵁ U}, {b ∈ T | ⊤ ≤ y b ⁻¹ᵁ U} ∈ 𝓝 t ∧
      DifferentiableAt ℂ (fun b => valAt' (y b) U f) t := by
    rintro t ⟨ht, hU⟩
    obtain ⟨B, hBT, htB, hB⟩ := h t ht
    have hn := (hB U f).1.mem_nhds (show t ∈ {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} from ⟨htB, hU⟩)
    exact ⟨mem_of_superset hn fun b hb => ⟨hBT hb.1, hb.2⟩, (hB U f).2.differentiableAt hn⟩
  exact ⟨isOpen_iff_mem_nhds.2 fun t ht => (key t ht).1, fun t ht => (key t ht).2.differentiableWithinAt⟩

theorem not_mem_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (w : (Σ k, ι k) → ℂ) :
    w ∉ mcPts (⊤ : Ideal (MRing ι)) := fun h => by
  simpa using h.2 1 trivial

theorem sat_iff {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {w w' : (Σ k, ι k) → ℂ} :
    w ∈ torusSat {w'} ↔ SameOrbit w w' :=
  ⟨fun ⟨_, e, a, ha, h⟩ => ⟨a, ha, by rw [h, Set.mem_singleton_iff.1 e]; rfl⟩, fun ⟨a, ha, h⟩ => ⟨w', rfl, a, ha, h⟩⟩

theorem analyticAt_comp {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {A : FinHolAtlas e X}
    {B : FinHolAtlas e Y} {ψ : X → Y} (hψ : HoloMap A B ψ) {U : Set Y} {f : Y → ℂ} (hf : B.HoloOn U f)
    (k : Fin A.n) {t : Fin e → ℂ} (ht : t ∈ (A.chart k).target) (htU : ψ ((A.chart k).symm t) ∈ U) :
    AnalyticAt ℂ (fun s => f (ψ ((A.chart k).symm s))) t := by
  obtain ⟨j, hj⟩ := B.cover (ψ ((A.chart k).symm t))
  have h1 : AnalyticAt ℂ (B.chart j ∘ ψ ∘ (A.chart k).symm) t := hψ.2 k j t ⟨ht, hj⟩
  have h2 : AnalyticAt ℂ (f ∘ (B.chart j).symm) ((B.chart j ∘ ψ ∘ (A.chart k).symm) t) :=
    hf j _ ⟨(B.chart j).map_source hj, by
      show (B.chart j).symm (B.chart j (ψ ((A.chart k).symm t))) ∈ U
      rwa [(B.chart j).left_inv hj]⟩
  refine (h2.comp h1).congr ?_
  have hc : ContinuousAt (fun s => ψ ((A.chart k).symm s)) t :=
    hψ.1.continuousAt.comp ((A.chart k).continuousAt_symm ht)
  filter_upwards [hc.eventually ((B.chart j).open_source.mem_nhds hj)] with s hs
  show f ((B.chart j).symm (B.chart j (ψ ((A.chart k).symm s)))) = _
  rw [(B.chart j).left_inv hs]

end Pts

open Pts

theorem ptsFam : PtsFam := by
  intro E _ _ _ H D l Xo c Y S RM Sys Fx Or ψ hJ hψ hπψ hψπ
  have hnJ : ∀ w, w ∉ mcPts Or.Re.J := fun w => by rw [hJ]; exact not_mem_top w
  choose z hz using fun x : Sys.X =>
    SheetDecomposition.exists_pt Or.𝔐 (Or.Re.R.mem (ψ x) (ψ x) (Or.Re.R.mem_U (ψ x)))
  have hol : ∀ k, IsHolTo (Sys.A.chart k).target fun t => z ((Sys.A.chart k).symm t) := fun k => by
    refine isHolTo_of_local fun t₀ ht₀ => ?_
    let w₀ := ψ ((Sys.A.chart k).symm t₀)
    have hB : IsOpen ((Sys.A.chart k).target ∩ (Sys.A.chart k).symm ⁻¹' (ψ ⁻¹' Or.Re.R.U w₀)) :=
      (Sys.A.chart k).symm.isOpen_inter_preimage ((Or.Re.R.isOpen_U w₀).preimage hψ.1)
    refine ⟨(Sys.A.chart k).target ∩ (Sys.A.chart k).symm ⁻¹' (ψ ⁻¹' Or.Re.R.U w₀), Set.inter_subset_left,
      ⟨ht₀, Or.Re.R.mem_U w₀⟩, ?_⟩
    refine _root_.GlobalTheory.CompanionTheory.Ar.PeriodsHol.isHolTo_of_coordsAt_family _ _ Or.𝔐.ξ _ _ RM.y Or.𝔐.tie Or.𝔐.all _ _
      (fun t => Or.Re.R.lift w₀ (ψ ((Sys.A.chart k).symm t))) _ hB ?_ ?_
    · refine differentiableOn_pi.2 fun p t ht => ?_
      exact (analyticAt_comp hψ (Or.Re.R.holo w₀ p) k ht.1 ht.2).differentiableAt.differentiableWithinAt
    · intro t ht
      exact SheetDecomposition.coords_of_sat Or.𝔐 (hz _) (sat_iff.2 (Or.Re.R.compat _ _ _ ⟨ht.2, Or.Re.R.mem_U _⟩))
  refine ⟨z, fun x x' e => ?_, hz, hol, fun U hU => ?_⟩
  · have h := sat_iff.1 (SheetDecomposition.sat_of_coords Or.𝔐 (hz x') (e ▸ hz x))
    rw [← hπψ x, Or.Re.R.inj _ _ (hnJ _) h, hπψ]
  · obtain ⟨g, hg, hgU⟩ := SheetDecomposition.ChartForm.exists_form Or.𝔐.tie U hU
    obtain ⟨w, hw, hwg⟩ := GroundTheory.Heights₂.Heights.HilbertSamuel.exists_mcPts_not_mem_mcPts (J := Ideal.span {g}) RM.arith
      (fun h => hg (h (Ideal.subset_span rfl)))
    have hg0 : MvPolynomial.aeval w g ≠ 0 := fun h0 => hwg ⟨hw.1, fun f hf => by
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hf
      have : MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) g) = 0 := by
        rw [MvPolynomial.eval_map]
        exact h0
      rw [map_mul, map_mul, this, mul_zero]⟩
    obtain ⟨w₁, hw₁⟩ := Or.Re.R.surj w hw (hnJ w)
    have hsym : SameOrbit w (Or.Re.R.lift w₁ w₁) := by
      obtain ⟨a, ha, h⟩ := hw₁
      refine ⟨fun k => (a k)⁻¹, fun k => inv_ne_zero (ha k), funext fun p => ?_⟩
      rw [h]
      simp only [inv_mul_cancel_left₀ (ha _)]
    have hc : CoordsAt Or.𝔐.ξ RM.y (z (Or.Re.π w₁)) w :=
      SheetDecomposition.coords_of_sat Or.𝔐 (hz _) (sat_iff.2 (by rw [hψπ]; exact hsym))
    have hx₀ : centre (z (Or.Re.π w₁)) ∈ U := hgU _ _ (Or.𝔐.all _) hc hg0
    obtain ⟨k, hk⟩ := Sys.A.cover (Or.Re.π w₁)
    have hopen := (Sys.A.chart k).isOpen_inter_preimage (hol k U 0).1
    have hd := (GlobalTheory.T.section_boundary_closed_and_codense _ _ Sys.A Sys.L Sys.s Sys.nb Sys.m Sys.W Sys.sec Sys.snc).2
    obtain ⟨x, ⟨hxs, -, hxU⟩, hxo⟩ := hd.inter_open_nonempty _ hopen ⟨Or.Re.π w₁, hk, (Sys.A.chart k).map_source hk, by
      show ⊤ ≤ z ((Sys.A.chart k).symm (Sys.A.chart k _)) ⁻¹ᵁ U
      rw [(Sys.A.chart k).left_inv hk]
      exact (SheetDecomposition.top_le_iff_pt _ _ _).2 hx₀⟩
    refine ⟨x, hxo, ?_⟩
    have h2 : ⊤ ≤ z ((Sys.A.chart k).symm (Sys.A.chart k x)) ⁻¹ᵁ U := hxU
    rw [(Sys.A.chart k).left_inv hxs] at h2
    exact (SheetDecomposition.top_le_iff_pt _ _ _).1 h2

end RootFieldNumerics
end
end

