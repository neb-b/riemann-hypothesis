module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MovedOfSplitPl
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSplitPlaceOfSplitPl
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0301

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RepsCompare

open GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting

section Generic

theorem moved_of_hom {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E)
    (hcc : ∀ x, c (c x) = x) (hc : c ≠ 1) (v : HeightOneSpectrum (𝓞 F)) (φ : E →+* v.adicCompletion F)
    (hφ : ∀ t : F, φ (algebraMap F E t) = algebraMap F (v.adicCompletion F) t)
    (hint : ∀ x : 𝓞 E, Valued.v (φ x) ≤ 1) (P : HeightOneSpectrum (𝓞 E))
    (hP : ∀ x : 𝓞 E, x ∈ P.asIdeal ↔ Valued.v (φ x) < 1) : GlobalTheory.UnRep.Moved c P.asIdeal := by
  by_contra hn
  let σ : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv c.toRingEquiv
  have hσ : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = c x := fun _ => rfl
  have one : ∀ b : 𝓞 E, b ∉ P.asIdeal → Valued.v (φ b) = 1 := fun b hb =>
    le_antisymm (hint b) (not_lt.1 fun h => hb ((hP b).2 h))
  have key : ∀ b : 𝓞 E, b ∉ P.asIdeal → σ b ∉ P.asIdeal := fun b hb h => hn ⟨σ b, h, b, (hcc _).symm, hb⟩
  obtain ⟨z, hz⟩ : ∃ z, c z ≠ z := by
    by_contra h
    exact hc (AlgEquiv.ext fun x => by simpa using not_exists.1 h x)
  have hab : φ z - φ (c z) ≠ 0 := sub_ne_zero.2 fun h => hz (φ.injective h).symm
  have hab' : Valued.v (φ z - φ (c z)) ≠ 0 := (Valuation.ne_zero_iff _).2 hab
  obtain ⟨t, ht⟩ : ∃ t : F, Valued.v (φ z - algebraMap F (v.adicCompletion F) t) < Valued.v (φ z - φ (c z)) := by
    have hd : DenseRange (algebraMap F (v.adicCompletion F)) := HeightOneSpectrum.denseRange_algebraMap (K := F) v
    have hN : {y : v.adicCompletion F | Valued.v (φ z - y) < Valued.v (φ z - φ (c z))} ∈ nhds (φ z) := by
      have ho := (Valued.isOpen_ball (v.adicCompletion F) (Valued.v.restrict (φ z - φ (c z)))).preimage
        (continuous_const.sub continuous_id : Continuous fun y : v.adicCompletion F => φ z - y)
      simp only [Set.preimage_ofPred_eq, Valuation.restrict_lt_iff] at ho
      refine ho.mem_nhds ?_
      show Valued.v (φ z - φ z) < _
      rw [sub_self, map_zero]
      exact zero_lt_iff.2 hab'
    obtain ⟨t, ht⟩ := hd.mem_nhds hN
    exact ⟨t, ht⟩
  have hb : Valued.v (φ (c z) - algebraMap F (v.adicCompletion F) t) = Valued.v (φ z - φ (c z)) := by
    rw [show φ (c z) - algebraMap F (v.adicCompletion F) t =
      (φ z - algebraMap F (v.adicCompletion F) t) - (φ z - φ (c z)) by ring]
    exact Valuation.map_sub_eq_of_lt_right _ ht
  have h1 : Valued.v (φ (z - algebraMap F E t)) < Valued.v (φ (c (z - algebraMap F E t))) := by
    rw [map_sub c, c.commutes, map_sub φ, map_sub φ, hφ, hb]
    exact ht
  generalize z - algebraMap F E t = u at h1
  obtain ⟨a, b, h⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq P (K := E) (u / c u)
  have hu : c u ≠ 0 := fun h0 => by
    rw [h0, map_zero, map_zero] at h1
    exact not_lt_zero h1
  refine absurd h1 (not_lt.2 ?_)
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hu, div_eq_iff hu] at h
  rcases h with h | h
  · have h2 : c u * (σ b.1 : 𝓞 E) = (σ a : 𝓞 E) * u := by
      have := congrArg c h
      rwa [map_mul, map_mul, hcc] at this
    have h3 := congrArg (fun x => Valued.v (φ x)) h2
    simp only [map_mul, one _ (key _ b.2), mul_one] at h3
    rw [h3]
    exact mul_le_of_le_one_left' (hint _)
  · have h2 : u * (a : E) = ((b.1 : 𝓞 E) : E) * c u := h
    have h3 := congrArg (fun x => Valued.v (φ x)) h2
    simp only [map_mul, one _ b.2, one_mul] at h3
    rw [← h3]
    exact mul_le_of_le_one_right' (hint _)

variable {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G)

end Generic

section Support

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem GlobalTheory.IdemPrime GlobalTheory.UnRep GlobalTheory.Member

variable {D : D7}

theorem finrank_two (D : D7) : Module.finrank D.host.F D.host.E = 2 :=
  Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield D.host.E) D.host.E

theorem cF_ne_one (D : D7) : cF D ≠ 1 := (latHat_eq_hat_and_gram D D.sp.X').2.2.2.2.2.2.1

theorem isSplitPl_iff (v : HeightOneSpectrum (𝓞 D.host.F)) : IsSplitPl D v ↔ SplitPl (cF D) v := by
  rw [Compare.splitPl_iff _ (finrank_two D) (cF_ne_one D)]
  constructor
  · rintro ⟨P, P', hne, h, h'⟩
    exact ⟨P.asIdeal, P'.asIdeal, fun e => hne (HeightOneSpectrum.ext e), P.isPrime, P'.isPrime,
      congrArg HeightOneSpectrum.asIdeal h, congrArg HeightOneSpectrum.asIdeal h'⟩
  · rintro ⟨w, w', hne, hw, hw', h, h'⟩
    have nb : ∀ u : Ideal (𝓞 D.host.E), u.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal → u ≠ ⊥ := by
      rintro u hu rfl
      apply v.ne_bot
      rw [← hu]
      exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
    exact ⟨⟨w, hw, nb w h⟩, ⟨w', hw', nb w' h'⟩, fun e => hne (congrArg HeightOneSpectrum.asIdeal e),
      HeightOneSpectrum.ext h, HeightOneSpectrum.ext h'⟩

theorem suppSplitOff_iff (V : HSp D) (N : ℕ) (g : Bridge.Gf V) : SuppSplitOff V N g ↔ SuppSplit (cF D) N g.1.1 := by
  rw [SuppSplit, Compare.support_iff (fun v => SplitPl (cF D) v ∧ (N : 𝓞 D.host.F) ∉ v.asIdeal), SuppSplitOff]
  simp only [isSplitPl_iff]
  exact Iff.rfl

theorem exists_splitAt_of_isIdemAt {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.L2.NTheta.IsIdemAt e P) :
    ∃ v, SplitAt D v e ∧ SplitPl (cF D) v ∧ P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal := by
  obtain ⟨v, he⟩ := (isSplitIdem_iff e).1 h.1
  obtain ⟨Q, hQ, hQv⟩ := exists_isIdemAt D v e he
  obtain rfl : P = Q := HeightOneSpectrum.ext (Ideal.ext fun x => by
    by_cases hx : x = 0
    · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
    · rw [h.2 x hx, hQ.2 x hx])
  obtain ⟨φ, hφ⟩ := exists_hom he
  refine ⟨v, he, ⟨P.asIdeal, P.isPrime, hQv,
    moved_of_hom (cF D) (fun x => star_star x) (cF_ne_one D) v φ (hom_algebraMap he hφ) (fun x => ?_) P fun x => ?_⟩, hQv⟩
  · rw [← mem_iff he, ← hφ, RingHom.map_mul]
    exact mul_mem_int (finPart_mem he) (AddSubgroup.subset_closure
      ⟨1, fun w => by rw [map_one]; exact one_mem _, x, rfl⟩)
  · by_cases hx : x = 0
    · subst hx
      refine iff_of_true (zero_mem _) ?_
      show Valued.v (φ 0) < 1
      rw [map_zero, map_zero]; exact zero_lt_one
    · have hx0 : Valued.v (φ x) ≠ 0 := by
        rw [Valuation.ne_zero_iff, map_ne_zero]
        exact fun h => hx (Subtype.ext h)
      rw [h.2 x hx, hφ, mem_iff he, map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 hx0)]

theorem finPart_sub_one (V : HSp D) (h : GA D V) (i j : Fin V.rank) :
    finPart D ((Formalism.L2.Theta.mt V h - 1) i j) = ((finHom V h).1 - 1) i j := by
  rw [Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub]
  congr 1
  by_cases e : i = j
  · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
  · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]

theorem suppSplitOff_of_splitOffBad (V : HSp D) (N : ℕ) (h : GA D V) (hs : FWT.SplitOffBad V N h) :
    SuppSplitOff V N (FWT.fin V h) := by
  classical
  obtain ⟨-, e, P, ⟨⟨es, hes, rfl⟩, -⟩, hN, hsupp⟩ := hs
  choose pv h1 h2 h3 using fun PP : P => exists_splitAt_of_isIdemAt (hes PP.1 PP.2)
  have hsum : ∑ PP ∈ P, es PP + cA D (∑ PP ∈ P, es PP) = fj D (∑ PP : P, singleV D.host.F (pv PP) 1) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, ← Finset.sum_add_distrib, ← Finset.sum_coe_sort P]
    exact Finset.sum_congr rfl fun PP _ => (h1 PP).2.2
  refine ⟨Finset.univ.image pv, fun v hv => ?_, fun v hv => ?_⟩
  · obtain ⟨PP, -, rfl⟩ := Finset.mem_image.1 hv
    refine ⟨(isSplitPl_iff _).2 (h2 PP), fun hm => hN PP.1 PP.2 ?_⟩
    rwa [← h3, Ideal.mem_comap, map_natCast] at hm
  · have h0 : evalV D.host.F v (∑ PP : P, singleV D.host.F (pv PP) 1) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_eq_zero fun PP _ => evalV_singleV_ne _ _ _ fun e =>
        hv (Finset.mem_image.2 ⟨PP, Finset.mem_univ _, e.symm⟩)
    generalize (∑ PP : P, singleV D.host.F (pv PP) 1) = α at hsum h0
    let π := Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E)
    rw [← Matrix.map_one π (map_zero _) (map_one _)]
    ext i j
    have h4 := congrArg (finPart D) (hsupp i j)
    rw [hsum, RingHom.map_mul, finPart_sub_one] at h4
    have h5 : π (finPart D (fj D α)) = 0 := by
      show evalV D.host.F v α ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      rw [h0, TensorProduct.zero_tmul]
    have h6 := congrArg π h4
    rw [map_mul, h5, zero_mul, Matrix.sub_apply, map_sub] at h6
    exact sub_eq_zero.1 h6.symm

theorem existsUnique_lift (V : HSp D) (g : Bridge.Gf V) : ∃! h : GA D V, h ∈ GfC V ∧ FWT.fin V h = g := by
  obtain ⟨_, x, rfl⟩ := g
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue V 1 _ (one_mem _) (GlobalTheory.UnitarySplit.finHom_mem V x)
  refine ⟨k, ⟨k1, Subtype.ext k2⟩, fun y hy => GlobalTheory.UnitarySplit.ga_ext V (hy.1.trans k1.symm) ?_⟩
  exact (congrArg Subtype.val hy.2).trans k2.symm

end Support

section Lattices

open GlobalTheory.AdLat GlobalTheory.UnRep GlobalTheory.UnRep.FullReps GlobalTheory.Member

variable {D : D7}

theorem inv_mulVec_mem_iff (V : HSp D) (g : Bridge.Gf V) (x : Fin V.rank → D.host.E) :
    (matF V g⁻¹).mulVec (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈
      Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (latC V : Set (Fin V.rank → D.host.E)) ↔ x ∈ latOf D.host.F g.1.1 (latC V) := by
  change (g.1⁻¹).1 *ᵥ fv D.host.F x ∈ hat D.host.F _ ↔ _
  constructor
  · intro hx
    exact ⟨_, hx, by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩
  · rintro ⟨z, hz, e⟩
    rw [← e, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact hz

theorem coe_hLat (V : HSp D) (g : Bridge.Gf V) :
    (Bridge.hLat V g : Set (Fin V.rank → D.host.E)) = latOf D.host.F g.1.1 (latC V) := by
  obtain ⟨-, -, hfg, hsp, -⟩ := latHat_eq_hat_and_gram D V
  obtain ⟨Λ, hΛ, -⟩ := exists_lattice_latOf D.host.F D.host.E V.rank (latC V) g.1 hfg hsp
  have : Bridge.hLat V g = Λ := by
    unfold Bridge.hLat
    rw [← Submodule.span_eq Λ, hΛ, ← coe_selfDualLatticeInFrameCoordinates_eq]
    congr 1
    exact Set.ext fun x => inv_mulVec_mem_iff V g x
  rw [this, hΛ]

theorem conj_mulVec_mem {R : Type} [CommRing R] {n : ℕ} (S : Subring R) (β : GL (Fin n) R) (y : GL (Fin n) S) (z : Fin n → R)
    (hz : ∀ j, ((β⁻¹).1 *ᵥ z) j ∈ S) (i : Fin n) :
    ((β⁻¹).1 *ᵥ ((β * Formalism.UG.bc S.subtype y * β⁻¹).1 *ᵥ z)) i ∈ S := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, Units.val_mul,
    ← Matrix.mulVec_mulVec]
  generalize (β⁻¹).1 *ᵥ z = w at hz
  exact Subring.sum_mem S (t := Finset.univ) (f := fun j => (y.1 i j : R) * w j) fun j _ => mul_mem (y.1 i j).2 (hz j)

theorem mulVec_mem_hat {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Lat V} (hβ : IsSDFrame V β Λ 1)
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) {k : Bridge.Gf V} (hk : k ∈ (levEnv V β L).J)
    {z : Fin V.rank → RA D.host.F D.host.E} (hz : z ∈ hat D.host.F (Λ : Set (Fin V.rank → D.host.E))) :
    k.1.1 *ᵥ z ∈ hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
  obtain ⟨c, hfr, -⟩ := hβ
  have h1 : Formalism.UG.bc (Lev.swapAE D) k.1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L L) := hk
  obtain ⟨y, hy⟩ := Formalism.L2.DIV.parLev_St h1.1
  have hy' : β * Formalism.L2.DIV.intGL D.host.F D.host.E V.rank y * β⁻¹ = Formalism.UG.bc (Lev.swapAE D) k.1 := hy
  have h2 := (hfr _).1 (GlobalTheory.PrincInLevel.swap_mem_hatL Λ z hz)
  have h3 : (Formalism.UG.bc (Lev.swapAE D) k.1).1 *ᵥ (fun i => Algebra.TensorProduct.comm D.host.F _ D.host.E (z i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
    rw [← hy']
    exact (hfr _).2 (conj_mulVec_mem _ β y _ h2)
  have h4 := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ h3
  convert h4 using 1
  funext i
  rw [AlgEquiv.eq_symm_apply]
  exact RingHom.map_mulVec (Lev.swapAE D) k.1.1 z i

theorem isUnA_gf (V : HSp D) (g : Bridge.Gf V) : IsUnA (cF D) V.gramᵀ g.1.1 := by
  obtain ⟨_, g, rfl⟩ := g
  intro x y
  rw [GlobalTheory.UnitarySplit.hermA_eq, GlobalTheory.UnitarySplit.hermA_eq]
  exact (RatElt.mem_UJ_iff _ _ _).1 (GlobalTheory.UnitarySplit.finHom_mem V g) y x

theorem isLattice_hLat (V : HSp D) (g : Bridge.Gf V) : Submodule.IsLattice D.host.E (Bridge.hLat V g) := by
  obtain ⟨-, -, hfg, hsp, -⟩ := latHat_eq_hat_and_gram D V
  obtain ⟨Λ, hΛ, h1, h2, -⟩ := exists_lattice_latOf D.host.F D.host.E V.rank (latC V) g.1 hfg hsp
  rw [SetLike.coe_injective ((coe_hLat V g).trans hΛ.symm)]
  exact Submodule.IsLattice.of_fg D.host.E h1

end Lattices

section Row

open Formalism.L2.DIV

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T)

end Row

end GlobalTheory.RepsCompare

end
