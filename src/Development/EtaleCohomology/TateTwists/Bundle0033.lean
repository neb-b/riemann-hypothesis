module

public import Development.EtaleCohomology.TateTwists.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.EtaleCohomology.TateTwists.Bundle0031
public import Development.EtaleCohomology.TateTwists.Bundle0017
public import Development.EtaleCohomology.TateTwists.Bundle0016

@[expose] public section

-- bundled from Development.EtaleCohomology.TateTwists.ColumnOf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleFoundations.columnPf

theorem vanish_fg {S : Type*} [CommRing S] {N G Pv : Type*} [AddCommGroup N] [Module S N] [AddCommGroup G] [Module S G]
    [AddCommGroup Pv] [Module S Pv] (φ : Pv →ₗ[S] N) {k : ℕ} (b : Fin k → G) (q : Fin k → Pv)
    (h : ∑ j, φ (q j) ⊗ₜ[S] b j = 0) :
    ∃ (gs : Finset N) (l : ℕ) (a : Fin k → Fin l → S) (c : gs → Fin l → S) (y : Fin l → G),
      (∀ j, b j = ∑ κ, a j κ • y κ) ∧ (∀ g, 0 = ∑ κ, c g κ • y κ) ∧
      ∀ κ, ∑ j, a j κ • φ (q j) + ∑ g, c g κ • (g : N) = 0 := by
  classical
  set Q0 : Submodule S N := Submodule.span S (Set.range fun j => φ (q j))
  have hQ0 : Q0.FG := Submodule.fg_span (Set.finite_range _)
  let t : Q0 ⊗[S] G := ∑ j, (⟨φ (q j), Submodule.subset_span ⟨j, rfl⟩⟩ : Q0) ⊗ₜ b j
  have ht : LinearMap.rTensor G Q0.subtype t = 0 := by simpa [t, map_sum] using h
  obtain ⟨Q, hQ0Q, hQ, ht'⟩ := TensorProduct.eq_zero_of_fg_of_subtype_eq_zero hQ0 ht
  obtain ⟨gs, hgs⟩ := hQ
  have memg : ∀ g : gs, (g : N) ∈ Q := fun g => hgs ▸ Submodule.subset_span g.2
  let m' : Fin k ⊕ gs → Q := Sum.elim (fun j => Submodule.inclusion hQ0Q ⟨φ (q j), Submodule.subset_span ⟨j, rfl⟩⟩)
    fun g => ⟨g, memg g⟩
  let n' : Fin k ⊕ gs → G := Sum.elim b fun _ => 0
  have hspan : Submodule.span S (Set.range m') = ⊤ := by
    apply Submodule.map_injective_of_injective Q.injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    refine le_antisymm (Submodule.span_le.2 ?_) ?_
    · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact (m' i).2
    · intro z hz
      rw [← hgs] at hz
      refine (Submodule.span_le.2 fun g hg => Submodule.subset_span ?_) hz
      exact ⟨m' (Sum.inr ⟨g, hg⟩), ⟨Sum.inr ⟨g, hg⟩, rfl⟩, rfl⟩
  have hsum : ∑ i, m' i ⊗ₜ[S] n' i = 0 := by
    rw [Fintype.sum_sum_type]
    simp only [m', n', Sum.elim_inl, Sum.elim_inr, TensorProduct.tmul_zero, Finset.sum_const_zero, add_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [t, map_sum] using ht'
  obtain ⟨l, a, y, hn, hm⟩ := TensorProduct.vanishesTrivially_of_sum_tmul_eq_zero S hspan hsum
  refine ⟨gs, l, fun j => a (Sum.inl j), fun g => a (Sum.inr g), y, fun j => hn (Sum.inl j), fun g => hn (Sum.inr g),
    fun κ => ?_⟩
  have := congrArg Subtype.val (hm κ)
  rw [Fintype.sum_sum_type] at this
  simpa [m'] using this

end LateralTheory.EtaleFoundations.columnPf

open LateralTheory.EtaleFoundations.columnPf in
theorem LateralTheory.EtaleFoundations.columnPf.kerLoc_of : kerLoc := by
  classical
  intro R _ M P φ hsurj hker G V u hu
  obtain ⟨k, b, q, rfl⟩ := TensorProduct.exists_sum_tmul_eq u
  have h : ∑ j, (φ.app (op V)).hom (q j) ⊗ₜ[ULift.{1} R] b j = 0 := by
    have := congrArg (TensorProduct.comm _ _ _) hu
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum] using this
  obtain ⟨gs, l, a, c, y, hb, hc, hrel⟩ := vanish_fg (φ.app (op V)).hom b q h
  refine loc_bind (loc_finset (Finset.univ : Finset gs) fun i _ => hsurj V (i : Sec M V)) ?_
  intro W hW hl
  choose pt hpt using hl
  have nφ : ∀ x, (φ.app (op W)).hom ((P.map hW.op).hom x) = (M.obj.map hW.op).hom ((φ.app (op V)).hom x) := fun x => by
    rw [← ModuleCat.comp_apply, φ.naturality, ModuleCat.comp_apply]
  let e : Fin l → P.obj (op W) := fun κ =>
    ∑ j, a j κ • (P.map hW.op).hom (q j) + ∑ g, c g κ • pt g (Finset.mem_univ g)
  have he : ∀ κ, (φ.app (op W)).hom (e κ) = 0 := fun κ => by
    have := congrArg (M.obj.map hW.op).hom (hrel κ)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, map_smul, map_zero] at this
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [e, map_add (f := _), map_sum, map_smul, nφ]
    rw [← this]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hpt g (Finset.mem_univ g)]
  have hu' : TensorProduct.map (G.obj.map hW.op).hom (P.map hW.op).hom (∑ j, b j ⊗ₜ[ULift.{1} R] q j) =
      ∑ κ, (G.obj.map hW.op).hom (y κ) ⊗ₜ e κ := by
    have hz : ∀ g : gs, ∑ κ, (G.obj.map hW.op).hom (y κ) ⊗ₜ[ULift.{1} R] (c g κ • pt g (Finset.mem_univ g)) = 0 :=
      fun g => by
        have := congrArg (fun z => (G.obj.map hW.op).hom z ⊗ₜ[ULift.{1} R] pt g (Finset.mem_univ g)) (hc g)
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_zero, TensorProduct.zero_tmul, map_sum, map_smul, TensorProduct.sum_tmul] at this
        rw [this]
        refine Finset.sum_congr rfl fun κ _ => ?_
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    simp only [e, TensorProduct.tmul_add, TensorProduct.tmul_sum, Finset.sum_add_distrib]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_comm (s := Finset.univ) (t := (Finset.univ : Finset gs)), Finset.sum_congr rfl fun g _ => hz g,
      Finset.sum_const_zero, add_zero, map_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [TensorProduct.map_tmul, hb j, map_sum, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  refine loc_mono (loc_finset (Finset.univ : Finset (Fin l)) fun κ _ => hker W (e κ) (he κ)) ?_
  intro W' k' hk'
  have hcomp : TensorProduct.map (G.obj.map (k' ≫ hW).op).hom (P.map (k' ≫ hW).op).hom
      (∑ j, b j ⊗ₜ[ULift.{1} R] q j) = TensorProduct.map (G.obj.map k'.op).hom (P.map k'.op).hom
      (TensorProduct.map (G.obj.map hW.op).hom (P.map hW.op).hom (∑ j, b j ⊗ₜ[ULift.{1} R] q j)) := by
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
    simp only [op_comp, Functor.map_comp, ModuleCat.hom_comp]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hcomp, hu', map_sum]
  refine Finset.sum_eq_zero fun κ _ => ?_
  rw [TensorProduct.map_tmul, hk' κ (Finset.mem_univ κ), TensorProduct.tmul_zero]

open LateralTheory.EtaleFoundations.columnPf in
theorem LateralTheory.EtaleFoundations.acyc.column_of : LateralTheory.EtaleFoundations.acyc.column := column_of' kerLoc_of
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleCupAlexanderWhitneyLeibnizOfSucc
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem awleib_ext_pf : EtaleSimplicialCochainEqOfEvaluationsAgree := by
  intro R _ E K k γ γ' H
  apply Cochain.ext
  intro p q hpq
  by_cases hp : ∃ N : ℕ, -(N : ℤ) = p
  · obtain ⟨N, rfl⟩ := hp
    rw [← cancel_epi (chainsXIso R E N).inv]
    apply Sheaf.hom_ext
    apply sheafify_hom_ext _ _ _ (K.X q).property
    ext U : 2
    apply ModuleCat.free_hom_ext
    intro x
    exact H N q hpq U.unop x.down
  · have hz : IsZero (((chains R).obj E).X p) :=
      HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => hp ⟨i, by
        have e : ComplexShape.embeddingDownNat.f i = -(i : ℤ) := rfl
        omega⟩)
    exact hz.eq_of_src _ _

theorem etale_cup_alexanderWhitney_leibniz_of_succ (hs : EtaleAlexanderWhitneyLeibnizPositiveSimplexDegree) : EtaleAlexanderWhitneyCupLeibnizRule :=
  etale_cup_alexanderWhitney_leibniz_of_ext_and_succ awleib_ext_pf hs

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTateTwistGeneratorRestrictionAndRootChangeH
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace LateralTheory.EtaleFoundations.GenIsoSurjRootPf

theorem ofRings_sec_res {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R))
    {V U : Scheme.{0}} (g : V ⟶ U) (x : M.obj Γ(U, ⊤)) :
    Sec.res g (ofRings.sec M U x) = ofRings.sec M V ((M.map g.appTop).hom x) := by
  have h := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality g.op
  have h2 := congrArg (fun f => f.hom x) h
  simp only [ModuleCat.hom_comp] at h2
  exact h2.symm

theorem res_twGen (q : ℕ) (j : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen j ζ) = twGen j (ζ.map g.appTop.hom) := by
  refine (ofRings_sec_res (twF q j) g _).trans ?_
  congr 1
  change Submodule.mapQ _ _ _ (twRel_le q j (Scheme.Hom.appTop g).hom) (Submodule.Quotient.mk _) = _
  rw [Submodule.mapQ_apply]
  simp [Finsupp.mapDomain_single]

theorem twGen_pow (q : ℕ) [NeZero q] (j : ℤ) {V : Scheme.{0}} (ζ ξ : Prim q Γ(V, ⊤)) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    twGen j ξ = ((a ^ j : (ZMod q)ˣ) : ZMod q).val • twGen j ζ := by
  have hrel : (Submodule.Quotient.mk (Finsupp.single ξ 1) : (twF q j).obj Γ(V, ⊤)) =
      Submodule.Quotient.mk (Finsupp.single ζ (ULift.up ((a ^ j : (ZMod q)ˣ) : ZMod q))) := by
    rw [Submodule.Quotient.eq]
    exact Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩
  have hs : (Finsupp.single ζ (ULift.up ((a ^ j : (ZMod q)ˣ) : ZMod q)) : Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) =
      ((a ^ j : (ZMod q)ˣ) : ZMod q).val • Finsupp.single ζ 1 := by
    rw [Finsupp.smul_single]
    congr 1
    apply ULift.ext
    simp only [nsmul_eq_mul, mul_one]
    exact (ZMod.natCast_zmod_val _).symm
  have key : ∀ (n : ℕ) (x y : (twF q j).obj Γ(V, ⊤)), x = n • y →
      ofRings.sec (twF q j) V x = n • ofRings.sec (twF q j) V y := by
    rintro n x y rfl
    exact map_nsmul _ _ _
  refine key _ _ _ ?_
  show (Submodule.Quotient.mk (Finsupp.single ξ 1) : (_ ⧸ twRel q j Γ(V, ⊤))) =
    _ • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (_ ⧸ twRel q j Γ(V, ⊤)))
  rw [hrel, hs]
  exact map_nsmul (Submodule.mkQ _) _ _

end LateralTheory.EtaleFoundations.GenIsoSurjRootPf

def LateralTheory.EtaleFoundations.EtalePrimitiveRootsLocallyPowersOfEachOther : Prop :=
  ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)),
    Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val

open LateralTheory.EtaleFoundations.GenIsoSurjRootPf in
theorem LateralTheory.EtaleFoundations.etale_tate_twist_generator_root_change_of_local_primitive_root_powers
    (hp : LateralTheory.EtaleFoundations.EtalePrimitiveRootsLocallyPowersOfEachOther) :
    LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorRestrictionAndRootChange := by
  intro q _ j
  refine ⟨fun V U g ζ => res_twGen q j g ζ, fun U ζ ξ => ?_⟩
  obtain ⟨S, hS, h⟩ := hp q U ζ ξ
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨a, ha⟩ := h V g hg
  exact ⟨_, (res_twGen q j g ξ).trans (twGen_pow q j (ζ.map g.appTop.hom) (ξ.map g.appTop.hom) a ha)⟩

namespace LateralTheory.EtaleFoundations.GenIsoSurjRootPf

theorem alg_prim_pow {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) (ζ ξ : A)
    (hζ : Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) (hξ : Polynomial.aeval ξ (Polynomial.cyclotomic q ℤ) = 0)
    {K : Type} [Field K] (f : A →+* K) : ∃ (a : (ZMod q)ˣ) (s : A), f s ≠ 0 ∧ s * (ξ - ζ ^ (a : ZMod q).val) = 0 := by
  have hqK : (q : K) ≠ 0 := by
    have := hq.map f; simpa using this.ne_zero
  have : NeZero (q : K) := ⟨hqK⟩
  have root : ∀ x : A, Polynomial.aeval x (Polynomial.cyclotomic q ℤ) = 0 → IsPrimitiveRoot (f x) q := by
    intro x hx
    rw [← Polynomial.isRoot_cyclotomic_iff, ← Polynomial.map_cyclotomic_int, Polynomial.IsRoot.def,
      Polynomial.eval_map]
    have h1 := congrArg f hx
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, map_zero] at h1
    rwa [show f.comp (algebraMap ℤ A) = Int.castRingHom K from RingHom.ext_int _ _] at h1
  have pq : ∀ x : A, Polynomial.aeval x (Polynomial.cyclotomic q ℤ) = 0 → x ^ q = 1 := by
    intro x hx
    obtain ⟨r, hr⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
    have := congrArg (Polynomial.aeval x) hr
    rw [map_mul, hx, zero_mul] at this
    simpa [sub_eq_zero] using this
  obtain ⟨i, hi, he⟩ := (root ζ hζ).eq_pow_of_pow_eq_one (root ξ hξ).pow_eq_one
  have hcop : i.Coprime q := by
    have h2 := root ξ hξ
    rw [← he] at h2
    exact ((root ζ hζ).pow_iff_coprime (NeZero.pos q) i).1 h2
  refine ⟨ZMod.unitOfCoprime i hcop, ∑ m ∈ Finset.range q, ξ ^ m * (ζ ^ i) ^ (q - 1 - m), ?_, ?_⟩
  · have hv : ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val = i := by
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
    intro h0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h0
    have : ∀ m ∈ Finset.range q, f (ξ ^ m * (ζ ^ i) ^ (q - 1 - m)) = (f ζ ^ i) ^ (q - 1) := by
      intro m hm
      rw [map_mul, map_pow, map_pow, map_pow, ← he, ← pow_add]
      congr 1
      have := Finset.mem_range.1 hm; omega
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h0
    rcases mul_eq_zero.1 h0 with h | h
    · exact hqK h
    · exact (root ζ hζ).ne_zero (NeZero.ne q) (eq_zero_of_pow_eq_zero (eq_zero_of_pow_eq_zero h))
  · have hv : ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val = i := by
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
    rw [hv, geom_sum₂_mul]
    rw [pq ξ hξ, ← pow_mul, mul_comm i q, pow_mul, pq ζ hζ, one_pow, sub_self]

theorem unit_res {U : Scheme.{0}} (s : Γ(U, ⊤)) : ∀ (O : U.Opens) (h : O ≤ ⊤), O = U.basicOpen s →
    IsUnit (U.presheaf.map (homOfLE h).op s) := by
  rintro O h rfl
  exact RingedSpace.isUnit_res_basicOpen U.toRingedSpace s

theorem loc_of_points {U : Scheme.{0}} (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (hP : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V), P V g → P W (k ≫ g))
    (h : ∀ x : U, ∃ s : Γ(U, ⊤), x ∈ U.basicOpen s ∧ P _ (U.basicOpen s).ι) : Loc U P := by
  choose s hs hPs using h
  let S : Sieve U := { arrows := fun V g => P V g, downward_closed := fun hg k => hP _ _ _ k hg }
  refine ⟨S, Scheme.zariskiTopology_le_etaleTopology _ ?_, fun V g hg => hg⟩
  rw [Scheme.mem_grothendieckTopology_iff]
  refine ⟨U.openCoverOfIsOpenCover (fun x => U.basicOpen (s x)) ?_, ?_⟩
  · exact eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hs x⟩
  · rintro V g ⟨x⟩
    exact hPs x

theorem prim_root_loc : LateralTheory.EtaleFoundations.EtalePrimitiveRootsLocallyPowersOfEachOther := by
  intro q _ U ζ ξ
  have hq : IsUnit (q : Γ(U, ⊤)) := ζ.2.1
  refine loc_of_points _ ?_ fun x => ?_
  · rintro V W g k ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [Scheme.Hom.comp_appTop]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, ha, map_pow]
  · obtain ⟨a, s, hs, hd⟩ := alg_prim_pow q hq ζ.1 ξ.1 ζ.2.2 ξ.2.2 (U.Γevaluation x).hom
    refine ⟨s, (U.evaluation_ne_zero_iff_mem_basicOpen x (show x ∈ (⊤ : U.Opens) from trivial) s).1 hs, a, ?_⟩
    have hu : IsUnit ((U.basicOpen s).ι.appTop.hom s) := unit_res s _ _ (by simp)
    have h0 := congrArg (U.basicOpen s).ι.appTop.hom hd
    rw [map_mul, map_zero, map_sub, map_pow] at h0
    exact sub_eq_zero.1 ((hu.mul_right_eq_zero).1 h0)

end LateralTheory.EtaleFoundations.GenIsoSurjRootPf

theorem LateralTheory.EtaleFoundations.etale_tate_twist_generator_restriction_and_root_change_holds : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorRestrictionAndRootChange :=
  LateralTheory.EtaleFoundations.etale_tate_twist_generator_root_change_of_local_primitive_root_powers LateralTheory.EtaleFoundations.GenIsoSurjRootPf.prim_root_loc
end
end

-- bundled from Development.EtaleCohomology.TateTwists.MuRootListProductOneSumEtaleLocallyZero
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.MuListPf

theorem ulift_natCast (q : ℕ) [NeZero q] (a : ZMod q) :
    ((a.val : ℕ) : ULift.{1} (ZMod q)) = ULift.up a := by
  apply ULift.ext
  show ((a.val : ℕ) : ULift.{1} (ZMod q)).down = a
  rw [ULift.down_natCast]
  exact ZMod.natCast_zmod_val a

theorem twGen_rel (q : ℕ) [NeZero q] (B : CommRingCat.{0}) (ζ ξ : Prim q B) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    twGenR B ξ = (a : ZMod q).val • twGenR B ζ := by
  have hm : Finsupp.single ξ (1 : ULift.{1} (ZMod q)) -
      Finsupp.single ζ (ULift.up ((a ^ (1 : ℤ) : (ZMod q)ˣ) : ZMod q)) ∈ twRel q 1 B :=
    Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩
  have h2 := (Submodule.Quotient.eq (twRel q 1 B)).2 hm
  simp only [zpow_one] at h2
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), ulift_natCast]
  change Submodule.Quotient.mk _ = _
  rw [h2]
  change _ = (ULift.up (a : ZMod q) : ULift.{1} (ZMod q)) •
    (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Prim q B →₀ ULift.{1} (ZMod q)) ⧸ twRel q 1 B)
  rw [← Submodule.Quotient.mk_smul, Finsupp.smul_single]
  congr 2
  exact (mul_one _).symm

theorem dvd_of_pow (q : ℕ) [NeZero q] (B : Type) [CommRing B] [Nontrivial B] (ζ : Prim q B) (n : ℕ)
    (h : ζ.1 ^ n = 1) : q ∣ n := by
  obtain ⟨-, -, h3, -, -, -⟩ := LateralTheory.Fin.PrimitiveRootsOfUnityBasicIdentities.intersectionNumber_baseChange q B
  by_contra hn
  have := h3 ζ n 0 (by rwa [Nat.modEq_zero_iff_dvd])
  rw [h, pow_zero, sub_self] at this
  exact not_isUnit_zero this

theorem sum_eq (q : ℕ) [NeZero q] (B : CommRingCat.{0}) (ζ : Prim q B) : ∀ (l : List (Prim q B)),
    (∀ ξ ∈ l, ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val) →
    ∃ n : ℕ, (l.map fun ξ => ξ.1).prod = ζ.1 ^ n ∧ (l.map fun ξ => twGenR B ξ).sum = n • twGenR B ζ := by
  intro l
  induction l with
  | nil => exact fun _ => ⟨0, by simp, by simp⟩
  | cons ξ l ih =>
    intro h
    obtain ⟨n, h1, h2⟩ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    obtain ⟨a, ha⟩ := h ξ List.mem_cons_self
    refine ⟨(a : ZMod q).val + n, ?_, ?_⟩
    · simp only [List.map_cons, List.prod_cons, h1, ha, pow_add]
    · simp only [List.map_cons, List.sum_cons, h2, twGen_rel q B ζ ξ a ha, add_smul]

theorem nontriv (V : Scheme.{0}) (x : V) : Nontrivial Γ(V, ⊤) :=
  (V.presheaf.germ ⊤ x trivial).hom.domain_nontrivial

theorem zero_of_dvd (q : ℕ) [NeZero q] (M : Type*) [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (n : ℕ) (hn : q ∣ n) (x : M) : n • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((n : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    apply ULift.ext
    rw [ULift.down_natCast]
    exact (ZMod.natCast_eq_zero_iff n q).2 hn
  rw [this, zero_smul]

end LateralTheory.EtaleFoundations.MuListPf

namespace LateralTheory.EtaleFoundations
open MuListPf

theorem mu_root_list_product_one_sum_etale_locally_zero : MuRootListProductOneSumEtaleLocallyZero := by
  intro q _ U l hl
  obtain ⟨hL1, hL2, -, -, hL5, hL6, hL7⟩ := LateralTheory.Fin.EtaleLocalPropertyBasicClosure.intersectionNumber_baseChange
  have stab : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V),
      ((twF q 1).map g.appTop).hom (l.map fun ζ => twGenR Γ(U, ⊤) ζ).sum = 0 →
      ((twF q 1).map (k ≫ g).appTop).hom (l.map fun ζ => twGenR Γ(U, ⊤) ζ).sum = 0 := by
    intro V W g k h
    rw [Scheme.Hom.comp_appTop, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, h, map_zero]
  cases l with
  | nil => exact hL1 _ _ fun V g => by simp
  | cons ζ l' =>
    have hloc : Loc U fun V g => ∀ ξ ∈ ζ :: l', ∃ a : (ZMod q)ˣ,
        g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val := by
      have := hL6 U (Fin (ζ :: l').length) (fun i V g => ∃ a : (ZMod q)ˣ,
          g.appTop.hom ((ζ :: l').get i).1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val)
        (fun i => ((LateralTheory.Fin.EtalePrimitiveRootsExistLocally.intersectionNumber_baseChange q U).2.1 ζ ((ζ :: l').get i)))
      refine hL2 _ _ _ this fun V g h ξ hξ => ?_
      obtain ⟨i, rfl⟩ := List.get_of_mem hξ
      exact h i
    refine hL5 U _ (hL2 _ _ _ hloc fun V g h => ?_)
    by_cases hV : IsEmpty V
    · exact hL7 V _
    · rw [not_isEmpty_iff] at hV
      obtain ⟨x⟩ := hV
      have := nontriv V x
      have key : ((twF q 1).map g.appTop).hom ((ζ :: l').map fun ζ => twGenR Γ(U, ⊤) ζ).sum = 0 := by
        rw [map_list_sum, List.map_map]
        have e : ((fun y => ((twF q 1).map g.appTop).hom y) ∘ fun ζ => twGenR Γ(U, ⊤) ζ) =
            (fun ξ => twGenR Γ(V, ⊤) ξ) ∘ Prim.map g.appTop.hom := by
          funext ξ; exact muK_gen_map q g.appTop ξ
        rw [e, ← List.map_map]
        obtain ⟨n, h1, h2⟩ := sum_eq q Γ(V, ⊤) (ζ.map g.appTop.hom) ((ζ :: l').map (Prim.map g.appTop.hom))
          (by
            intro ξ' hξ'
            obtain ⟨ξ, hξ, rfl⟩ := List.mem_map.1 hξ'
            exact h ξ hξ)
        rw [h2]
        apply zero_of_dvd q
        apply dvd_of_pow q Γ(V, ⊤) (ζ.map g.appTop.hom) n
        rw [← h1]
        refine Eq.trans ?_ ((congrArg g.appTop.hom hl).trans (map_one _))
        rw [map_list_prod, List.map_map, List.map_map]
        rfl
      exact hL1 _ _ fun W k => stab V W g k key

end LateralTheory.EtaleFoundations
end

