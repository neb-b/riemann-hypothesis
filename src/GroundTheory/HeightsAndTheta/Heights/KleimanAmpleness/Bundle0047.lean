module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeVanishCone
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistSplitCech
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0041
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0035

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeVanishLoc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section LocE

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  (M : FinGradedSub (S := S) (x := x) E)

def locConeE (I : Finset (Fin (N + 1))) (hI : I ⊆ support x) :
    LocMod S N M.coneSubE I →ₗ[Poly S N] ConeE S x E :=
  LocalizedModule.lift (monos I) M.coneSubE.subtype fun s => by
    rw [Module.End.isUnit_iff]
    obtain ⟨e, he⟩ := monos_isHomogeneous s.2
    exact bijective_smul_of_isHomogeneous he (aeval_ne_zero_of_mem_monos_support hI s.2)

theorem locConeE_mk (I : Finset (Fin (N + 1))) (hI : I ⊆ support x) (m : M.coneSubE)
    (s : monos (S := S) I) :
    (s : Poly S N) • locConeE M I hI (LocalizedModule.mk m s) = m := by
  have h1 : (s : Poly S N) • (LocalizedModule.mk m s : LocalizedModule (monos (S := S) I) M.coneSubE) =
      LocalizedModule.mk m 1 := by
    rw [LocalizedModule.smul'_mk]
    exact LocalizedModule.mk_cancel s m
  have h2 : locConeE M I hI ((s : Poly S N) • LocalizedModule.mk m s) = m := by
    change LocalizedModule.lift (monos I) M.coneSubE.subtype _
      ((s : Poly S N) • (LocalizedModule.mk m s : LocalizedModule (monos (S := S) I) M.coneSubE)) = m
    rw [h1]
    simp
  have h3 := (locConeE M I hI).map_smul (s : Poly S N) (LocalizedModule.mk m s : LocMod S N M.coneSubE I)
  exact h3.symm.trans h2

theorem locConeE_mk_eq {I : Finset (Fin (N + 1))} (hI : I ⊆ support x) {m : M.coneSubE}
    {s : monos (S := S) I} {w : ConeE S x E} (h : (s : Poly S N) • w = m) :
    locConeE M I hI (LocalizedModule.mk m s) = w := by
  obtain ⟨e, he⟩ := monos_isHomogeneous s.2
  exact (bijective_smul_of_isHomogeneous he (aeval_ne_zero_of_mem_monos_support hI s.2)).1
    ((locConeE_mk M I hI m s).trans h.symm)

theorem locConeE_injective (I : Finset (Fin (N + 1))) (hI : I ⊆ support x) :
    Function.Injective (locConeE M I hI) := by
  refine (injective_iff_map_eq_zero _).mpr fun z => ?_
  refine LocalizedModule.induction_on
    (β := fun z : LocalizedModule (monos (S := S) I) M.coneSubE => locConeE M I hI z = 0 → z = 0)
    (fun m s hz => ?_) z
  have h := locConeE_mk M I hI m s
  rw [hz, smul_zero] at h
  have hm : m = 0 := Subtype.ext h.symm
  rw [hm, LocalizedModule.zero_mk]

theorem locConeE_locRes {I J : Finset (Fin (N + 1))} (h : I ⊆ J) (hJ : J ⊆ support x)
    (z : LocMod S N M.coneSubE I) :
    locConeE M J hJ (locRes h z) = locConeE M I (h.trans hJ) z := by
  refine LocalizedModule.induction_on
    (β := fun z : LocalizedModule (monos (S := S) I) M.coneSubE =>
      locConeE M J hJ (locRes h z) = locConeE M I (h.trans hJ) z) (fun m s => ?_) z
  rw [locRes_mk]
  exact locConeE_mk_eq M hJ (locConeE_mk M I _ m s)

theorem locModE_subsingleton {I : Finset (Fin (N + 1))} {i : Fin (N + 1)} (hi : i ∈ I) (hx : x i = 0) :
    Subsingleton (LocMod S N M.coneSubE I) := by
  have hX : ∀ m : M.coneSubE, (X i : Poly S N) • m = 0 := fun m => by
    apply Subtype.ext
    refine coneE_ext fun d => ?_
    change coeffE S x E d ((X i : Poly S N) • (m : ConeE S x E)) = coeffE S x E d 0
    rw [coeffE_smul_of_isHomogeneous (isHomogeneous_X S i), aeval_X, hx, zero_smul, map_zero]
  refine subsingleton_of_forall_eq 0 fun z => ?_
  refine LocalizedModule.induction_on
    (β := fun z : LocalizedModule (monos (S := S) I) M.coneSubE => z = 0) (fun m s => ?_) z
  rw [← LocalizedModule.mk_cancel_common_left ⟨X i, X_mem_monos hi⟩ s m]
  have h0 : (⟨X i, X_mem_monos hi⟩ : monos (S := S) I) • m = 0 := hX m
  rw [h0, LocalizedModule.zero_mk]

theorem locConeE_degLoc (c : ℤ) (I : StdCell N) (hI : I.1 ⊆ support x) {z : LocMod S N M.coneSubE I.1}
    (hz : z ∈ degLoc M.coneGradedE c I) :
    ∃ v ∈ M.tilde c ⟨I.1, I.2.1, hI⟩, locConeE M I.1 hI z = singleE S x E c v := by
  refine Submodule.span_induction (p := fun z _ => ∃ v ∈ M.tilde c ⟨I.1, I.2.1, hI⟩,
    locConeE M I.1 hI z = singleE S x E c v) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨m, s, a, e, hm, hse, hae, rfl⟩
    have hs0 := aeval_ne_zero_of_mem_monos_support hI s.2
    refine ⟨(aeval x (s : Poly S N))⁻¹ • coeffE S x E a (m : ConeE S x E),
      Submodule.subset_span ⟨coeffE S x E a m, s, a, e, s.2, hse, m.2 a, hae, rfl⟩, locConeE_mk_eq M hI ?_⟩
    rw [smul_singleE hse, smul_smul, mul_inv_cancel₀ hs0, one_smul, show c + (e : ℤ) = a by omega]
    exact (M.eq_singleE_of_mem_conePieceE hm).symm
  · exact ⟨0, zero_mem _, by rw [map_zero, map_zero]⟩
  · rintro _ _ _ _ ⟨v, hv, hzv⟩ ⟨v', hv', hzv'⟩
    exact ⟨v + v', add_mem hv hv', by rw [map_add (f := _), map_add (f := _), hzv, hzv']⟩
  · rintro s _ _ ⟨v, hv, hzv⟩
    refine ⟨s • v, ?_, by rw [LinearMap.map_smul_of_tower, hzv, map_smul]⟩
    rw [← algebraMap_smul Ω s v]
    exact (M.tilde c _).smul_mem (algebraMap S (chartRing S x ⟨I.1, I.2.1, hI⟩) s) hv

def tildeGensE (c : ℤ) (I : Chart x) : Set E :=
  {y | ∃ (m : E) (s : Poly S N) (a : ℤ) (e : ℕ), s ∈ monos I.1 ∧ s.IsHomogeneous e ∧ m ∈ M.piece a ∧
    a - e = c ∧ y = (aeval x s)⁻¹ • m}

theorem tildeE_le_span (c : ℤ) (I : Chart x) :
    (M.tilde c I : Set E) ⊆ Submodule.span S (tildeGensE M c I) := by
  have hclosed : ∀ a : chartRing S x I, ∀ y ∈ Submodule.span S (tildeGensE M c I),
      a • y ∈ Submodule.span S (tildeGensE M c I) := by
    intro a y hy
    refine Submodule.span_induction (p := fun y _ => a • y ∈ Submodule.span S (tildeGensE M c I))
      ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨m, s, b, e, hs, hse, hm, hbe, rfl⟩
      obtain ⟨f, s', e', hs', hf, hse', ha⟩ := a.2
      refine Submodule.subset_span ⟨aeval x f • m, s' * s, b + e', e' + e, mul_mem hs' hs, hse'.mul hse,
        M.smul_mem e' b f m hf hm, by push_cast; omega, ?_⟩
      change (a : Ω) • ((aeval x s)⁻¹ • m) = _
      rw [smul_smul, smul_smul, ha, map_mul, mul_inv, div_eq_mul_inv]
      congr 1
      ring
    · rw [smul_zero]; exact zero_mem _
    · intro y y' _ _ hy hy'; rw [smul_add]; exact add_mem hy hy'
    · intro t y _ hy
      have : a • (t • y) = t • (a • y) := by
        rw [← algebraMap_smul Ω t y, ← algebraMap_smul Ω t (a • y)]
        change (a : Ω) • (algebraMap S Ω t • y) = algebraMap S Ω t • ((a : Ω) • y)
        rw [smul_smul, smul_smul, mul_comm]
      rw [this]; exact Submodule.smul_mem _ t hy
  intro y hy
  exact Submodule.span_induction (p := fun y _ => y ∈ Submodule.span S (tildeGensE M c I))
    (fun y hy => Submodule.subset_span hy) (zero_mem _) (fun _ _ _ _ => add_mem)
    (fun a y _ hy => hclosed a y hy) hy

theorem exists_locConeE_eq (c : ℤ) (I : StdCell N) (hI : I.1 ⊆ support x) {y : E}
    (hy : y ∈ M.tilde c ⟨I.1, I.2.1, hI⟩) :
    ∃ z ∈ degLoc M.coneGradedE c I, locConeE M I.1 hI z = singleE S x E c y := by
  refine Submodule.span_induction (p := fun y _ => ∃ z ∈ degLoc M.coneGradedE c I,
    locConeE M I.1 hI z = singleE S x E c y) ?_ ?_ ?_ ?_ (tildeE_le_span M c _ hy)
  · rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    refine ⟨LocalizedModule.mk ⟨singleE S x E a m, M.singleE_mem_coneSubE hm⟩ ⟨s, hs⟩,
      Submodule.subset_span ⟨_, ⟨s, hs⟩, a, e, M.singleE_mem_conePieceE hm, hse, hae, rfl⟩,
      locConeE_mk_eq M hI ?_⟩
    have hs0 := aeval_ne_zero_of_mem_monos_support hI hs
    change s • singleE S x E c ((aeval x s)⁻¹ • m) = singleE S x E a m
    rw [smul_singleE hse, smul_smul, mul_inv_cancel₀ hs0, one_smul, show c + (e : ℤ) = a by omega]
  · exact ⟨0, zero_mem _, by rw [map_zero, map_zero]⟩
  · rintro _ _ _ _ ⟨z, hz, hzy⟩ ⟨z', hz', hzy'⟩
    exact ⟨z + z', add_mem hz hz', by rw [map_add (f := _), map_add (f := _), hzy, hzy']⟩
  · rintro t _ _ ⟨z, hz, hzy⟩
    exact ⟨t • z, Submodule.smul_mem _ t hz, by rw [LinearMap.map_smul_of_tower, hzy, map_smul]⟩

end LocE

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistSplit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Retract

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {r : ℕ} (η : Fin (r + 1) → Ω) (M₀ : FinGradedSub (S := S) (x := x) Ω) (n : ℕ) (c : ℤ)
  {G B : SubSystem S x Ω} (hG : ∀ I, M₀.tilde 0 I = G.sub I)
  (hB : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I)


include hG hB in
theorem twist_retract (i : ℕ) :
    ∃ (ι : ((G.twist (B.pow n)).twist (twistSys S x c)).H i →+ cohom (twGraded η M₀) i c)
      (π : cohom (twGraded η M₀) i c →+ ((G.twist (B.pow n)).twist (twistSys S x c)).H i),
      ∀ z, π (ι z) = z := by
  have hker : ∀ z : Cech.Cochain (fun K : Chart x => ↥(((G.twist (B.pow n)).twist (twistSys S x c)).sub K)) i,
      Cech.d _ ((G.twist (B.pow n)).twist (twistSys S x c)).res i z = 0 →
      Cech.d _ locResS i (Fmap η M₀ n c hG hB i z) = 0 := by
    intro z hz
    rw [← F_d, hz, Fmap_zero]
  have hker' : ∀ (s : Cech.Cochain (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀)) i)
      (hs : s ∈ Cech.Cdeg (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀)) (degLoc (twGraded η M₀) c) i),
      Cech.d _ locResS i s = 0 →
      Cech.d _ ((G.twist (B.pow n)).twist (twistSys S x c)).res i (Gm η M₀ n c hG hB i s hs) = 0 := by
    intro s hs h0
    rw [← Gm_d η M₀ n c hG hB i s hs (by rw [h0]; exact Submodule.zero_mem _)]
    funext K
    apply Subtype.ext
    change gm η M₀ n c (i + 1) (Cech.d _ locResS i s) K = 0
    rw [h0, gm_zero]
  let f : LinearMap.ker (Cech.d (fun K : Chart x => ↥(((G.twist (B.pow n)).twist (twistSys S x c)).sub K))
        ((G.twist (B.pow n)).twist (twistSys S x c)).res i) →+
      Cech.cocyDeg (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀)) (degLoc (twGraded η M₀) c) locResS i :=
    { toFun := fun z => ⟨Fmap η M₀ n c hG hB i z.1, Submodule.mem_inf.mpr
        ⟨LinearMap.mem_ker.mpr (hker z.1 (LinearMap.mem_ker.mp z.2)), Fmap_mem η M₀ n c hG hB i z.1⟩⟩
      map_zero' := Subtype.ext (Fmap_zero η M₀ n c hG hB i)
      map_add' := fun a b => Subtype.ext (Fmap_add η M₀ n c hG hB i a.1 b.1) }
  let g : Cech.cocyDeg (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀)) (degLoc (twGraded η M₀) c) locResS i →+
      LinearMap.ker (Cech.d (fun K : Chart x => ↥(((G.twist (B.pow n)).twist (twistSys S x c)).sub K))
        ((G.twist (B.pow n)).twist (twistSys S x c)).res i) :=
    { toFun := fun y => ⟨Gm η M₀ n c hG hB i y.1 (Submodule.mem_inf.mp y.2).2,
        LinearMap.mem_ker.mpr (hker' _ _ (LinearMap.mem_ker.mp (Submodule.mem_inf.mp y.2).1))⟩
      map_zero' := Subtype.ext (funext fun K => Subtype.ext (gm_zero η M₀ n c i K))
      map_add' := fun a b => Subtype.ext (funext fun K => Subtype.ext (gm_add η M₀ n c i a.1 b.1 K)) }
  set_option synthInstance.maxHeartbeats 200000 in
    refine quot_retract _ _ f g ?_ ?_ ?_
    · intro z hz
      exact F_bdry η M₀ n c hG hB i z.1 hz
    · intro y hy
      exact G_bdry η M₀ n c hG hB i y.1 (Submodule.mem_inf.mp y.2).2 hy
    · intro z
      apply Subtype.ext
      funext K
      apply Subtype.ext
      exact gm_Fmap η M₀ n c hG hB i z.1 K

end Retract

theorem TwistSplit.proof : TwistSplit.Statement := by
  intro S _ _ Ω _ _ N x M₀ G B r η hG _ hB
  refine ⟨TwM η M₀, inferInstance, inferInstance, inferInstance, inferInstance, twGraded η M₀, inferInstance, ?_⟩
  intro b c i
  exact twist_retract η M₀ b c hG hB i

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PZChartSmul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

theorem ZChartSmul.proof : ZChartSmul.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ G H r h hh J j hj I a ha z hz
  classical
  have hmem : ∀ l, h l ∈ H.sub I := fun l => (Submodule.mem_iInf _).mp (hh l) I
  refine Submodule.span_induction (p := fun z _ => a • z ∈ secsOnZChart G H h I J) ?_ ?_ ?_ ?_ hz
  · rintro e ⟨m, hm⟩
    obtain ⟨n, hn⟩ := Set.mem_iInter.mp ha I
    rw [one_mul] at hn
    set u := ∏ l ∈ J.1.erase j, h l with hu
    have hxu : xProd J = h j * u := (Finset.mul_prod_erase J.1 h hj).symm
    have hk : J.1.card = (J.1.erase j).card + 1 := by
      rw [Finset.card_erase_of_mem hj]
      have := Finset.card_pos.mpr ⟨j, hj⟩
      omega
    have hun : u ^ n ∈ (H.pow ((J.1.erase j).card * n)).sub I :=
      AmpleTwistLocal.pow_mem_pow H I (VeryAmpleZTwist.prod_mem_pow H I hmem _) n
    have hw : a * h j ^ n * u ^ n ∈ (H.pow (n + (J.1.erase j).card * n)).sub I :=
      AmpleTwistLocal.mul_mem_pow H I hn _ hun
    have h1 := VeryAmpleZTwist.smul_mem_twist_pow G H I hw hm
    refine Submodule.subset_span ⟨m + n, ?_⟩
    have e1 : xProd J ^ (m + n) • a • e = (a * h j ^ n * u ^ n) • xProd J ^ m • e := by
      rw [smul_smul, smul_smul, hxu]; ring_nf
    have e2 : J.1.card * (m + n) = J.1.card * m + (n + (J.1.erase j).card * n) := by
      rw [hk]; ring
    rw [e1, e2]
    exact h1
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro b c _ _ hb hc; rw [smul_add]; exact Submodule.add_mem _ hb hc
  · intro s y _ hy; rw [smul_comm]; exact Submodule.smul_mem _ s hy

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SecsTwistSysPtX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

noncomputable section

def BundleRealises {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {K : Type} [Fintype K]
    [DecidableEq K] {ι : K → Type} (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} {x : Fin (N + 1) → Ω}
    (Q : Kleiman.LineBundle S x) (β : K → ℤ) : Prop :=
  ∀ c : ℤ, (Q.toSubSystem.twist (Kleiman.twistSys S x c)).secs =
    secOver S y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)

section Graph

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N m : ℕ} {x : Fin (N + 1) → Ω}

theorem realises_graph (Q : Kleiman.LineBundle S x) (n : ℤ) (s : Fin m → Ω) (hgen : IsGraphGen Q n s) :
    BundleRealises (graphVec x s) baseBlock Q (graphDeg n) :=
  fun c => twist_secs_eq_secOver Q n s hgen c

end Graph

section Point

variable (k : Type) [Field k]

end Point

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreLiftVal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime)

noncomputable section

section Objects

variable {K : Type} [Fintype K] (ι : K → Type)

abbrev segreIdx : Unit ⊕ K → Type := Sum.elim (fun _ : Unit => ∀ k, ι k) ι

variable (R : Type*) [CommRing R]

def segreIncl : MRing ι R →ₐ[R] MRing (segreIdx ι) R :=
  rename fun v => (⟨Sum.inr v.1, v.2⟩ : Σ k, segreIdx ι k)

variable {ι R}

def segreY (c : ∀ k, ι k) : MRing (segreIdx ι) R :=
  X (⟨Sum.inl (), c⟩ : Σ k, segreIdx ι k)

def segreMon (c : ∀ k, ι k) : MRing (segreIdx ι) R :=
  ∏ k, X (⟨Sum.inr k, c k⟩ : Σ k, segreIdx ι k)

variable (ι R)

def segreRels : Set (MRing (segreIdx ι) R) :=
  {g | ∃ c d : ∀ k, ι k, g = segreY c * segreMon d - segreY d * segreMon c}

def segreLiftVal (W : Ideal (MRing ι R)) : (Σ k, segreIdx ι k) → Polynomial (MRing ι R ⧸ W)
  | ⟨Sum.inl _, c⟩ => Polynomial.X * Polynomial.C (Ideal.Quotient.mk W (∏ k, X ⟨k, c k⟩))
  | ⟨Sum.inr k, i⟩ => Polynomial.C (Ideal.Quotient.mk W (X ⟨k, i⟩))

def segreLiftMap (W : Ideal (MRing ι R)) :
    MRing (segreIdx ι) R →ₐ[R] Polynomial (MRing ι R ⧸ W) :=
  aeval (segreLiftVal ι R W)

def segreLift (W : Ideal (MRing ι R)) : Ideal (MRing (segreIdx ι) R) :=
  RingHom.ker (segreLiftMap ι R W)

end Objects

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

