module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DChKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.KoszulThreeOfDet
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.koszulThree_of_det :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (al : Fin T.q → Fin n → x.A), T.ProL → T.Eig x al → K3 Λ.h k := by
  intro l _ L G0 T Λ n x k al hP hE
  intro z hz
  have hρ : ∀ g, x.ρX x.A g = mat x.ρ g := by
    intro g
    ext i j
    simp [NP.ρX]
  have hzero : ∀ j, z (Λ.ta j) = 0 := by
    intro j
    have hc := Λ.comm j
    have h1 := hz.2.2.1 (Λ.ph j) (Λ.ta j)
    have h2 := hz.2.2.1 (Λ.ta j) (Λ.ph j)
    rw [hc] at h1
    simp only [hρ, map_inv, Λ.p_ta, Λ.p_ph, map_one, inv_one, one_mul, mul_one] at h1 h2
    rw [h2] at h1
    have h3 : z (Λ.ta j) = mat x.ρ (T.sg j) * z (Λ.ta j) * mat x.ρ (T.sg j)⁻¹ := by
      have := h1
      rw [add_comm (z (Λ.ta j))] at this
      exact add_left_cancel this
    have hPZ : mat x.ρ (T.sg j) * z (Λ.ta j) = z (Λ.ta j) * mat x.ρ (T.sg j) := by
      conv_rhs => rw [h3]
      rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
    exact od_comm x.A n x.a (mat x.ρ (T.sg j)) (z (Λ.ta j)) (al j) (x.blk _) (hz.1 _)
      (hE j).1 (hE j).2 hPZ
  obtain ⟨y, hy⟩ := coc_ker l L Λ.G G0 Λ.h n x (Set.range Λ.ta) z
    (by rw [← Set.range_comp]; exact ker_oo l L G0 T Λ hP)
    (by
      rintro a ⟨j, rfl⟩
      exact ⟨Λ.p_ta j, hzero j⟩)
    hz
  have hzy : (fun g => y (Λ.h.p₀ g)) = z := funext hy
  have hy' : y ∈ SelZ G0.frame x.t (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (Od x.A x.A n x.a) := by
    rw [← Glob.Hom.sel_iff Λ.h, hzy]
    exact hz
  obtain ⟨s, c, hsc⟩ := k.gen y hy'
  refine ⟨s, c, ?_⟩
  have hb := (Glob.Hom.bd_iff Λ.h (x.ρX x.A) (Od x.A x.A n x.a) _).mpr hsc
  show _ ∈ Bd Λ.G.frame (fun g => x.ρX x.A (Λ.h.p₀ g)) (Od x.A x.A n x.a)
  convert hb using 1
  funext g
  simp [hy]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.NonssDesc
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem md_surj {R G G' : Type} [CommRing R] [Group G] [Group G'] (p : G →* G') (hp : Function.Surjective p) :
    Function.Surjective (MonoidAlgebra.mapDomainRingHom R p) := by
  intro x
  induction x using MonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add a b ha hb =>
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    exact ⟨a' + b', map_add _ _ _⟩
  | single g c =>
    obtain ⟨g', rfl⟩ := hp g
    exact ⟨MonoidAlgebra.single g' c, by simp⟩

private theorem md_ker {R G G' : Type} [CommRing R] [Group G] [Group G'] (p : G →* G') (hp : Function.Surjective p)
    (J : TwoSidedIdeal (MonoidAlgebra R G)) (hJ : ∀ k, p k = 1 → MonoidAlgebra.single k 1 - 1 ∈ J)
    (z : MonoidAlgebra R G) (hz : MonoidAlgebra.mapDomainRingHom R p z = 0) : z ∈ J := by
  choose s hs using hp
  have key : ∀ z : MonoidAlgebra R G,
      z - MonoidAlgebra.mapDomain s (MonoidAlgebra.mapDomainRingHom R p z) ∈ J := by
    intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      rw [map_add (f := _), MonoidAlgebra.mapDomain_add, add_sub_add_comm]
      exact J.add_mem ha hb
    | single g c =>
      have h := J.mul_mem_left (MonoidAlgebra.single (s (p g)) c) _ (hJ ((s (p g))⁻¹ * g) (by simp [hs]))
      rw [mul_sub, MonoidAlgebra.single_mul_single, mul_one, mul_one, mul_inv_cancel_left] at h
      simpa using h
  have := key z
  rw [hz] at this
  simpa using this

private theorem md_span {R G G' : Type} [CommRing R] [Group G] [Group G'] (p : G →* G') (hp : Function.Surjective p)
    (J : TwoSidedIdeal (MonoidAlgebra R G)) (hJ : ∀ k, p k = 1 → MonoidAlgebra.single k 1 - 1 ∈ J)
    (S : Set (MonoidAlgebra R G')) (hS : ∀ y ∈ S, ∃ x ∈ J, MonoidAlgebra.mapDomainRingHom R p x = y)
    (z : MonoidAlgebra R G) (hz : MonoidAlgebra.mapDomainRingHom R p z ∈ TwoSidedIdeal.span S) : z ∈ J := by
  have key : ∀ y ∈ TwoSidedIdeal.span S, ∃ x ∈ J, MonoidAlgebra.mapDomainRingHom R p x = y := by
    intro y hy
    induction hy using TwoSidedIdeal.span_induction with
    | mem y hy => exact hS y hy
    | zero => exact ⟨0, J.zero_mem, map_zero _⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', h1, rfl⟩ := ha
      obtain ⟨b', h2, rfl⟩ := hb
      exact ⟨a' + b', J.add_mem h1 h2, map_add _ _ _⟩
    | neg a _ ha =>
      obtain ⟨a', h1, rfl⟩ := ha
      exact ⟨-a', J.neg_mem h1, map_neg _ _⟩
    | left_absorb c a _ ha =>
      obtain ⟨a', h1, rfl⟩ := ha
      obtain ⟨c', rfl⟩ := md_surj (R := R) p hp c
      exact ⟨c' * a', J.mul_mem_left _ _ h1, map_mul _ _ _⟩
    | right_absorb c a _ ha =>
      obtain ⟨a', h1, rfl⟩ := ha
      obtain ⟨c', rfl⟩ := md_surj (R := R) p hp c
      exact ⟨a' * c', J.mul_mem_right _ _ h1, map_mul _ _ _⟩
  obtain ⟨x, hx, e⟩ := key _ hz
  have := J.add_mem (md_ker p hp J hJ (z - x) (by rw [map_sub, e, sub_self])) hx
  rwa [sub_add_cancel] at this

private theorem nonSS_down {R G G' : Type} [CommRing R] [Group G] [Group G'] (p : G →* G') (hp : Function.Surjective p)
    (I : Set (MonoidAlgebra R G)) (I' : Set (MonoidAlgebra R G'))
    (hk : ∀ k, p k = 1 → MonoidAlgebra.single k 1 - 1 ∈ I)
    (hI : ∀ z, MonoidAlgebra.mapDomainRingHom R p z ∈ I' → z ∈ I) (Q : Ideal R) :
    NonSS I (RingHom.id R) Q → NonSS I' (RingHom.id R) Q := by
  rintro ⟨κ, hκ, f, hf, hn⟩
  refine ⟨κ, hκ, f, hf, fun hs => hn ?_⟩
  rw [RingHom.comp_id] at hs ⊢
  set J := TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G f '' I) with hJ
  set J' := TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G' f '' I') with hJ'
  have hcomm : ∀ w : MonoidAlgebra R G,
      MonoidAlgebra.mapDomainRingHom κ p (MonoidAlgebra.mapRingHom G f w) =
        MonoidAlgebra.mapRingHom G' f (MonoidAlgebra.mapDomainRingHom R p w) := by
    intro w
    induction w using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g c => simp
  have hkJ : ∀ k, p k = 1 → MonoidAlgebra.single k 1 - 1 ∈ J := fun k h =>
    TwoSidedIdeal.subset_span ⟨_, hk k h, by rw [map_sub, map_one, MonoidAlgebra.mapRingHom_single, map_one]⟩
  have hpre : ∀ z, MonoidAlgebra.mapDomainRingHom κ p z ∈ J' → z ∈ J := by
    refine md_span p hp J hkJ _ ?_
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, rfl⟩ := md_surj (R := R) p hp y
    exact ⟨_, TwoSidedIdeal.subset_span ⟨x, hI x hy, rfl⟩, hcomm x⟩
  have hs' := md_surj (R := κ) p hp
  have hle : RingHom.ker (MonoidAlgebra.mapDomainRingHom κ p) ≤ RingHom.ker J.ringCon.mk' := by
    intro z hz
    rw [RingHom.mem_ker] at hz ⊢
    have h1 : z - 0 ∈ J := by rw [sub_zero]; exact md_ker p hp J hkJ z hz
    exact (RingCon.eq _).2 ((TwoSidedIdeal.rel_iff _ _ _).2 h1)
  let ψ : MonoidAlgebra κ G' →+* J.ringCon.Quotient :=
    (MonoidAlgebra.mapDomainRingHom κ p).liftOfSurjective hs' ⟨J.ringCon.mk', hle⟩
  have hψ : ∀ x, ψ (MonoidAlgebra.mapDomainRingHom κ p x) = J.ringCon.mk' x := fun x =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ x
  have hker : J'.ringCon ≤ RingCon.ker ψ := by
    intro a b hab
    rw [RingCon.ker_apply]
    obtain ⟨a, rfl⟩ := hs' a
    obtain ⟨b, rfl⟩ := hs' b
    have h1 := (TwoSidedIdeal.rel_iff _ _ _).1 hab
    rw [← map_sub] at h1
    rw [hψ, hψ]
    exact (RingCon.eq _).2 ((TwoSidedIdeal.rel_iff _ _ _).2 (hpre _ h1))
  refine RingHom.isSemisimpleRing_of_surjective (RingCon.lift _ ψ hker) ?_
  intro y
  obtain ⟨x, rfl⟩ := RingCon.mk'_surjective _ y
  exact ⟨((MonoidAlgebra.mapDomainRingHom κ p x : MonoidAlgebra κ G') : J'.ringCon.Quotient), hψ x⟩

private theorem closure_down {R G G' : Type} [CommRing R] [Group G] [Group G'] [TopologicalSpace G] [TopologicalSpace G']
    (p : G →* G') (hp : Function.Surjective p) (ho : IsOpenMap p) (m : Ideal R)
    (S : Set (MonoidAlgebra R G)) (S' : Set (MonoidAlgebra R G'))
    (hk : ∀ k, p k = 1 → MonoidAlgebra.single k 1 - 1 ∈ closureIdeal m S)
    (hS : ∀ y ∈ S', ∃ x ∈ S, MonoidAlgebra.mapDomainRingHom R p x = y)
    (z : MonoidAlgebra R G) (hz : MonoidAlgebra.mapDomainRingHom R p z ∈ closureIdeal m S') : z ∈ closureIdeal m S := by
  simp only [closureIdeal, TwoSidedIdeal.mem_iInf] at hk hz ⊢
  intro N V
  let V' : OpenNormalSubgroup G' :=
    { toSubgroup := V.toSubgroup.map p
      isOpen' := ho _ V.isOpen'
      isNormal' := V.isNormal'.map p hp }
  refine md_span p hp _ (fun k h => hk k h N V) _ ?_ z (hz N V')
  rintro y ((hy | ⟨a, ha, rfl⟩) | ⟨_, ⟨h, hh, rfl⟩, rfl⟩)
  · obtain ⟨x, hx, e⟩ := hS y hy
    exact ⟨x, TwoSidedIdeal.subset_span (Or.inl (Or.inl hx)), e⟩
  · exact ⟨MonoidAlgebra.single 1 a, TwoSidedIdeal.subset_span (Or.inl (Or.inr ⟨a, ha, rfl⟩)), by simp⟩
  · exact ⟨MonoidAlgebra.single h 1 - 1, TwoSidedIdeal.subset_span (Or.inr ⟨h, hh, rfl⟩), by
      rw [map_sub, map_one]; simp⟩

theorem UpperTheory.V.Pa.nonss_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G' : Glob l L) (g : G.Hom G') (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G.frame O n) (r' : Resid G'.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (u' : Pair r' B) (H : Subgroup G.Γ) [H.Normal], IsOpen (H : Set G.Γ) → H ≤ G.η.ker → (∀ a : G.G₀, (a : G.Γ) ∈ H → ∀ i, r.chib i a = 1) → g.p.ker = PL l H → Glob.Compat g r r' → u'.D.comap g.p₀ = u.D → u'.ψ = u.ψ → ∀ q : Ideal B, (NonSS (augmentationIdealKernel u) (RingHom.id B) q → NonSS (augmentationIdealKernel u') (RingHom.id B) q) ∧ (DiscSt u.D q ↔ DiscSt u'.D q) := by
  intro l _ L G G' g n O _ _ _ _ _ r r' B _ _ _ u u' H _ hHo hHle hHchi hker hcomp hD hψ q
  refine ⟨?_, ?_⟩
  · have hk : ∀ k : G.G₀, g.p₀ k = 1 → MonoidAlgebra.single k 1 - 1 ∈ u.D.chBar (pairGens u) := fun k h =>
      pl_chBar l L G n O r B u H hHo hHle hHchi _ k (by
        rw [← hker, MonoidHom.mem_ker]; exact congrArg Subtype.val h)
    have ho : IsOpenMap g.p₀ := (MonoidHom.isOpenQuotientMap_of_isQuotientMap g.p₀_quot).isOpenMap
    obtain ⟨hst, hoel, -⟩ := map_star l L G G' g n O B
    have hCH := ((comap_lam n B _ _ g.p₀ u'.D).2.2.2.2.2 g.p₀_surj).2
    rw [hD] at hCH
    refine nonSS_down g.p₀ g.p₀_surj _ _ hk (fun z hz => ?_) q
    refine closure_down g.p₀ g.p₀_surj ho _ _ _ hk ?_ z hz
    rintro y (hy | ⟨v, a, h⟩ | ⟨w, _, ⟨⟨a, ha, rfl⟩, hb⟩, h⟩)
    · rw [← hCH] at hy
      obtain ⟨x, hx, e⟩ := hy
      exact ⟨x, Or.inl hx, e⟩
    · rw [hψ] at h
      rcases h with rfl | rfl
      · exact ⟨_, Or.inr (Or.inl ⟨v, a, Or.inl rfl⟩), hoel v _ a⟩
      · exact ⟨_, Or.inr (Or.inl ⟨v, a, Or.inr rfl⟩), by rw [hst]; exact congrArg _ (hoel v _ a)⟩
    · have hm : G.φu w a ∈ r.Ip w := by
        refine ⟨⟨a, ha, rfl⟩, Subgroup.mem_iInf.2 fun i => ?_⟩
        have hb' : r'.chib i (G'.φu w a) = 1 := Subgroup.mem_iInf.1 hb i
        have e1 : r.chib i (G.φu w a) = r'.chib i (g.p₀ (G.φu w a)) := DFunLike.congr_fun (hcomp.1 i) _
        rw [g.p₀_φu] at e1
        exact e1.trans hb'
      have e : MonoidAlgebra.mapDomainRingHom B g.p₀ (MonoidAlgebra.single (G.φu w a) 1) =
          MonoidAlgebra.single (G'.φu w a) 1 := by
        rw [← g.p₀_φu]; simp
      rcases h with rfl | rfl
      · exact ⟨_, Or.inr (Or.inr ⟨w, _, hm, Or.inl rfl⟩), by rw [map_sub, map_one, e]⟩
      · exact ⟨_, Or.inr (Or.inr ⟨w, _, hm, Or.inr rfl⟩), by rw [map_sub, map_one, hst, e]⟩
  · rw [← hD]
    exact (BC.discSt_map n B B _ u'.D).2.1 _ g.p₀ g.p₀_surj q
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.NpDesc
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem np_desc_sep {K : Type} [Field K] (a : PowerSeries K)
    (h : ∀ m : ℕ, a ∈ (Ideal.span {(PowerSeries.X : PowerSeries K)}) ^ m) : a = 0 := by
  ext i
  have := h (i + 1)
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at this
  simpa using this i (Nat.lt_succ_self i)

theorem UpperTheory.V.Pa.np_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G' : Glob l L) (g : G.Hom G') (n : ℕ) (x : NP G.frame n) (k : Kap x) (H : Subgroup G.Γ) [H.Normal], IsOpen (H : Set G.Γ) → H ≤ G.η.ker → x.UnipOn H → g.p.ker = PL l H → (∃ ρ' : G'.G₀ →* GL (Fin n) x.A, ∀ a, ρ' (g.p₀ a) = x.ρ a) ∧ ∃ κ' : Fin k.g → G'.G₀ → Matrix (Fin n) (Fin n) x.A, ∀ j a, κ' j (g.p₀ a) = k.κ j a := by
  intro l _ L G G' g n x k H _ hH hη hU hker
  have hρ : ∀ d, x.ρX x.A d = mat x.ρ d := by
    intro d
    ext i j
    simp [NP.ρX]
  obtain ⟨hR, -, -, -⟩ := rho_hom l G.frame n x k x.A
  have hl : (l : x.A) = 0 := by
    have := (am_fin l G.frame n x 0 0).2.2.2.2.1
    simpa using this
  have hunip : ∀ (m : ℕ) (h : G.G₀), (h : G.Γ) ∈ H → ∃ e, ∀ i j,
      (x.ρX x.A (h ^ l ^ e) - 1) i j ∈ (Ideal.span {algebraMap x.A x.A x.t}) ^ m := by
    intro m h hh
    obtain ⟨e, he⟩ := hU m h hh
    refine ⟨e, fun i j => ?_⟩
    rw [hρ, show algebraMap x.A x.A x.t = x.t from rfl, Ideal.span_singleton_pow]
    exact he i j
  have sep : ∀ a : x.A, (∀ m, a ∈ (Ideal.span {algebraMap x.A x.A x.t}) ^ m) → a = 0 :=
    fun a h => np_desc_sep a h
  have key : ∀ d : G.G₀, g.p₀ d = 1 → x.ρ d = 1 ∧ ∀ j, k.κ j d = 0 := by
    intro d hd
    have hdP : (d : G.Γ) ∈ PL l H := by
      rw [← hker, MonoidHom.mem_ker, ← Glob.Hom.coe_p₀, hd]
      rfl
    constructor
    · have h0 := (coc_pl l L G n x.A _ (x.ρX x.A) (fun _ => 0) H hH hη hl hR.1 hR.2.1 hR.2.2 hunip
        (fun i j N => IsLocallyConstant.const _) (fun a b => by simp)).2 d hdP
      apply Units.ext
      have hm : x.ρX x.A d = 1 :=
        Matrix.ext fun i j => sub_eq_zero.mp (sep _ (fun m => (h0 m i j).1))
      rw [hρ] at hm
      exact hm
    · intro j
      have hj := (coc_pl l L G n x.A _ (x.ρX x.A) (k.κ j) H hH hη hl hR.1 hR.2.1 hR.2.2 hunip
        (k.mem j).2.1 (k.mem j).2.2.1).2 d hdP
      exact Matrix.ext fun a b => sep _ (fun m => (hj m a b).2)
  have hkerρ : g.p₀.ker ≤ x.ρ.ker := fun d hd => (key d hd).1
  let e := QuotientGroup.quotientKerEquivOfSurjective g.p₀ g.p₀_surj
  refine ⟨⟨(QuotientGroup.lift g.p₀.ker x.ρ hkerρ).comp e.symm.toMonoidHom, fun a => ?_⟩,
    ⟨fun j b => k.κ j (Classical.choose (g.p₀_surj b)), fun j a => ?_⟩⟩
  · have hs : e.symm (g.p₀ a) = (QuotientGroup.mk a : G.G₀ ⧸ g.p₀.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift g.p₀.ker x.ρ hkerρ (e.symm (g.p₀ a)) = x.ρ a
    rw [hs]
    rfl
  · have hc : g.p₀ (Classical.choose (g.p₀_surj (g.p₀ a))) = g.p₀ a :=
      Classical.choose_spec (g.p₀_surj (g.p₀ a))
    set c := Classical.choose (g.p₀_surj (g.p₀ a))
    have hd : g.p₀ (c⁻¹ * a) = 1 := by rw [map_mul, map_inv, hc, inv_mul_cancel]
    have h3 := (k.mem j).2.2.1 c (c⁻¹ * a)
    rw [mul_inv_cancel_left, (key _ hd).2 j] at h3
    simp at h3
    exact h3.symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PairDesc
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem md_single {B G G' : Type} [CommRing B] [Group G] [Group G'] (f : G →* G') (a : G) :
    MonoidAlgebra.mapDomainRingHom B f (MonoidAlgebra.single a 1) = MonoidAlgebra.single (f a) 1 := by
  simp

theorem UpperTheory.V.Pa.pair_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G' : Glob l L) (g : G.Hom G') (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G.frame O n) (r' : Resid G'.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (H : Subgroup G.Γ) [H.Normal], IsOpen (H : Set G.Γ) → H ≤ G.η.ker → (∀ a : G.G₀, (a : G.Γ) ∈ H → ∀ i, r.chib i a = 1) → g.p.ker = PL l H → Glob.Compat g r r' → ∃ u' : Pair r' B, u'.D.comap g.p₀ = u.D ∧ u'.ψ = u.ψ := by
  intro l _ L G G' g n O _ _ _ _ _ r r' B _ _ _ u H _ hHo hHη hHχ hker hc
  obtain ⟨hc1, hc2, hc3⟩ := hc
  have hkill : ∀ k : G.G₀, g.p₀ k = 1 → u.D.Kills (MonoidAlgebra.single k 1 - 1) := by
    intro k hk
    have hk' : (k : G.Γ) ∈ PL l H := by
      rw [← hker, MonoidHom.mem_ker, ← g.coe_p₀, hk]; rfl
    have h1 := pl_chBar l L G n O r B u H hHo hHη hHχ ∅ k hk'
    refine UpperTheory.V.CA.d_closed u.D (maximalIdeal B) u.cont (u.D.CH ∪ ∅) ?_ _ h1
    rintro z (hz | hz)
    · refine (UpperTheory.V.CA.d_toDet u.D z).2.2.2.1 ((UpperTheory.V.CA.d_ker _ z).1.1 (UpperTheory.V.CA.d_ch_ker _ ?_))
      rw [UpperTheory.V.CA.d_toDet_CH]
      exact TwoSidedIdeal.subset_span hz
    · exact hz.elim
  obtain ⟨D', hD'⟩ := gdet_desc n B G.G₀ G'.G₀ g.p₀ u.D g.p₀_surj hkill
  obtain ⟨-, hlam, htr, hmap, -, -⟩ := comap_lam n B G.G₀ G'.G₀ g.p₀ D'
  rw [hD'] at hlam htr hmap
  obtain ⟨hstar, hoEl, -, -⟩ := map_star l L G G' g n O B
  refine ⟨{ D := D', ψ := u.ψ, cont := ?_, red := ?_, psi := ?_, P := ?_, Ord := ?_, I := ?_ }, hD', rfl⟩
  · intro i
    refine (g.adicCont_iff _ fun a => D'.lam i (MonoidAlgebra.single a 1)).1 ?_
    have : (fun a => D'.lam i (MonoidAlgebra.single (g.p₀ a) 1)) =
        fun a : G.G₀ => u.D.lam i (MonoidAlgebra.single a 1) := funext fun a => by
      rw [hlam, md_single]
    rw [this]
    exact u.cont i
  · obtain ⟨-, -, -, -, hrep, hinj⟩ := comap_lam n (ResidueField O) G.G₀ G'.G₀ g.p₀ r'.Dbar
    refine (hinj g.p₀_surj).1 _ ?_
    rw [← hmap]
    refine u.red.trans ?_
    unfold Resid.Dbar
    rw [hrep]
    congr 1
    ext a i j
    simp only [diagRep, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.comp_apply, hc1]
  · intro v i
    refine ⟨(u.psi v i).cont, fun a => ?_, fun a => ?_⟩
    · rw [← hc2]; exact (u.psi v i).red a
    · rw [← hc3]; exact (u.psi v i).mu a
  · intro i a
    obtain ⟨a, rfl⟩ := g.p₀_surj a
    rw [← md_single, ← hstar, ← hlam, ← hlam]
    exact u.P i a
  · intro v a h
    obtain ⟨h, rfl⟩ := g.p₀_surj h
    rw [← md_single, ← hoEl, ← map_mul, ← htr]
    exact u.Ord v a h
  · rintro w _ ⟨⟨a, ha, rfl⟩, ha'⟩ h
    obtain ⟨h, rfl⟩ := g.p₀_surj h
    have hmem : G.φu w a ∈ r.Ip w := by
      refine ⟨⟨a, ha, rfl⟩, Subgroup.mem_iInf.2 fun i => ?_⟩
      have := Subgroup.mem_iInf.1 ha' i
      rw [MonoidHom.mem_ker] at this ⊢
      rw [hc1, MonoidHom.comp_apply, g.p₀_φu]
      exact this
    have := u.I w _ hmem h
    rw [htr, map_mul, map_sub, map_one, md_single, md_single, g.p₀_φu] at this
    exact this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PtUnip
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem chi_ofRep_single {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ (Polynomial A) _).det = _
  rw [map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly, Matrix.charmatrix]
  congr 2
  · ext1 a b
    by_cases hab : a = b <;> simp [GDet.repAlg, hab, Matrix.one_apply, Matrix.diagonal_apply]
  · ext1 a b
    simp [GDet.repAlg]

private theorem kills_max {B K : Type} [CommRing B] [IsLocalRing B] [Field K] [Finite K] (g : B →+* K) (b : B)
    (hb : b ∈ maximalIdeal B) : g b = 0 := by
  by_contra h
  haveI := Fintype.ofFinite K
  have h1 := FiniteField.pow_card_sub_one_eq_one (g b) h
  have h2 : Fintype.card K - 1 ≠ 0 := by have := Fintype.one_lt_card (α := K); omega
  have h3 : IsUnit (1 - b ^ (Fintype.card K - 1)) :=
    isUnit_one_sub_self_of_mem_nonunits _ (Ideal.pow_mem_of_mem _ hb _ (Nat.pos_of_ne_zero h2))
  have h4 := h3.map g
  rw [map_sub, map_one, map_pow, h1, sub_self] at h4
  exact not_isUnit_zero h4

theorem UpperTheory.V.Pa.pt_unip :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (D0 : ℕ) (P : Pt T u D0), Adapted T (r := r) → P.x.UnipOn T.H.toSubgroup := by
  intro l _ L G0 T n O _ _ _ r B _ _ _ u D0 P hA
  refine UpperTheory.V.Pa.unip_of l G0.frame n P.x _ fun h hh => ?_
  have key : ∀ {C : Type} [CommRing C] (f : B →+* C), (u.D.map f).chi (MonoidAlgebra.single h 1) =
      (u.D.chi (MonoidAlgebra.single h 1)).map f := fun f => by
    have := ((UpperTheory.V.CA.d_gmap u.D).2.2.1 f (MonoidAlgebra.single h 1)).1
    rwa [MonoidAlgebra.mapRingHom_single, map_one] at this
  have h1 := key P.f.toRingHom
  rw [P.maps.1, chi_ofRep_single] at h1
  have h2 := key (res O B : B →+* ResidueField O)
  rw [u.red, Resid.Dbar, chi_ofRep_single] at h2
  have h3 : (UpperTheory.V.W.diagRep r.chib) h = 1 := by
    change Matrix.diagonal (fun i => ((r.chib i h : (ResidueField O)ˣ) : ResidueField O)) = 1
    simp [hA.1 h hh]
  rw [h3, Matrix.charpoly_one, Fintype.card_fin] at h2
  have h4 : (u.D.chi (MonoidAlgebra.single h 1) - (Polynomial.X - 1) ^ n).map (res O B : B →+* ResidueField O) = 0 := by
    rw [Polynomial.map_sub, ← h2]
    simp
  have h5 : (u.D.chi (MonoidAlgebra.single h 1) - (Polynomial.X - 1) ^ n).map
      ((PowerSeries.constantCoeff : P.x.A →+* P.x.K).comp P.f.toRingHom) = 0 := by
    ext k
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    refine kills_max _ _ ((res_eq_zero_iff O B _).1 ?_)
    have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p k) h4
    simpa only [Polynomial.coeff_map, Polynomial.coeff_zero, RingHom.coe_coe] using this
  rw [Polynomial.map_sub, sub_eq_zero] at h5
  rw [h1, Polynomial.map_map, h5]
  simp
end

