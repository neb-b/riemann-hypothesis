module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0344
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0343

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PImageOne
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.imageOne_of :
    ImageOne := by
  intro Z P S k b _ _ _
  have hk : IsFinite k := IsFinite.of_comp k b
  have ht : IsFinite k.toImage := by
    have : IsFinite (k.toImage ≫ k.imageι) := by rw [k.toImage_imageι]; exact hk
    exact IsFinite.of_comp k.toImage k.imageι
  have hs : Surjective k.toImage :=
     surjective_of_isDominant_of_isClosed_range k.toImage k.toImage.isClosedMap.isClosed_range
  have e : k.toImage ≫ (k.imageι ≫ b) = k ≫ b := k.toImage_imageι_assoc b
  have huc : UniversallyClosed (k.imageι ≫ b) := by
    have : UniversallyClosed (k.toImage ≫ (k.imageι ≫ b)) := by rw [e]; infer_instance
    exact UniversallyClosed.of_comp_surjective k.toImage _
  have hqf : LocallyQuasiFinite (k.imageι ≫ b) := by
    refine .of_finite_preimage_singleton _ fun s => ?_
    refine (((k ≫ b).finite_preimage_singleton s).image k.toImage).subset ?_
    intro y hy
    obtain ⟨x, rfl⟩ := k.toImage.surjective y
    refine ⟨x, ?_, rfl⟩
    have : (k ≫ b) x = (k.imageι ≫ b) (k.toImage x) := by
      rw [← e, Scheme.Hom.comp_apply]
    exact this.trans hy
  have : IsProper (k.imageι ≫ b) := ⟨⟩
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite _, ht⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PImgBasic
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

namespace UpperTheory.Gal.TranscendenceTraces

private noncomputable def toOf {Z S : Scheme.{0}} {p : Z ⟶ S} (A : Sq p) : A.To (Sq.of p A.u) :=
  ⟨𝟙 _, pullback.lift A.v A.r A.pb.w, Category.id_comp _, pullback.lift_fst _ _ _,
    (pullback.lift_snd _ _ _).trans (Category.comp_id _).symm⟩

private noncomputable def ofTo {Z S V U : Scheme.{0}} (p : Z ⟶ S) (g : V ⟶ U) (u : U ⟶ S) :
    (Sq.of p (g ≫ u)).To (Sq.of p u) :=
  ⟨g, pullback.lift (pullback.fst p (g ≫ u)) (pullback.snd p (g ≫ u) ≫ g)
      (pullback.condition.trans (Category.assoc _ _ _).symm),
    rfl, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

private noncomputable def imgVal {Z S : Scheme.{0}} {p : Z ⟶ S} {R' R : Type} [CommRing R'] [CommRing R] {I : Cx R'} {J : Cx R}
    (τ : Fam p I J) {n : ℤ} (α : Cochain ((chains R').obj (sch.obj Z)) I n) (k : ℕ) (s : ℤ) (h : -(k : ℤ) + n = s)
    (U : Scheme.{0}) (u : U ⟶ S) : Sec (J.X s) U :=
  (τ.deg s).app (Sq.of p u) (ev (R := R') α k s h (pullback p u) (pullback.fst p u))

end UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.imgBasic_of :
    ImgBasic := by
  intro Z S p R' R _ _ I J τ n
  have ev_def {T : Type} [CommRing T] {E : Spc} {K : Cx T} {j : ℤ}
      (α : Cochain ((chains T).obj E) K j) (k : ℕ) (s : ℤ) (h : -(k : ℤ) + j = s)
      (U : Scheme.{0}) (x : Sx E k U) : ev (R := T) α k s h U x =
        Sec.map ((chainsXIso T E k).inv ≫ α.v _ _ h) (freeGen T _ U x) := rfl
  refine ⟨fun α => ?_, fun m hm α β hαβ => ?_⟩
  · have ev_res (k : ℕ) (s : ℤ) (h : -(k : ℤ) + n = s) {V U : Scheme.{0}}
        (g : V ⟶ U) (x : Sx (sch.obj Z) k U) :
        Sec.res g (ev (R := R') α k s h U x) = ev (R := R') α k s h V (Sx.res g x) := by
      rw [ev_def, CupSpec.map_res, CupSpec.freeGen_res]
      rfl
    have ev_ext (β' β : Cochain ((chains R).obj (sch.obj S)) J n)
        (he : ∀ k s h U x, ev (R := R) β' k s h U x = ev (R := R) β k s h U x) : β' = β := by
      ext i s hs : 1
      by_cases hi : i ≤ 0
      · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = -(k : ℤ) := ⟨(-i).toNat, by omega⟩
        rw [← cancel_epi (chainsXIso R (sch.obj S) k).inv]
        exact CupSpec.free_ext _ _ (fun U x => he k s hs U x)
      · exact (CupSpec.isZero_chains (sch.obj S) i (by omega)).eq_of_src _ _
    have hnat : ∀ (k : ℕ) (s : ℤ) (h : -(k : ℤ) + n = s) (V U : Scheme) (g : V ⟶ U) (u : Sx (sch.obj S) k U),
        Sec.res g (imgVal τ α k s h U u) = imgVal τ α k s h V (Sx.res g u) := by
      intro k s h V U g u
      have e1 : Sec.res g ((τ.deg s).app (Sq.of p u) (ev (R := R') α k s h (pullback p u) (pullback.fst p u))) =
          (τ.deg s).app (Sq.of p (g ≫ u)) (Sec.res (ofTo p g u).k (ev (R := R') α k s h (pullback p u) (pullback.fst p u))) :=
        (τ.deg s).nat (ofTo p g u) _
      have e2 : Sec.res (ofTo p g u).k (ev (R := R') α k s h (pullback p u) (pullback.fst p u)) =
          ev (R := R') α k s h (pullback p (g ≫ u)) (pullback.fst p (g ≫ u)) := by
        refine (ev_res k s h (ofTo p g u).k (pullback.fst p u)).trans ?_
        congr 1
        show (ofTo p g u).k ≫ pullback.fst p u = pullback.fst p (g ≫ u)
        exact pullback.lift_fst _ _ _
      exact e1.trans (congrArg _ e2)
    have hex := exists_cochain_ev_eq_of_natural R (E := sch.obj S) (I := J) (n := n)
      (imgVal τ α) hnat
    obtain ⟨β, hβ⟩ := hex
    have hIm : τ.IsImage α β := by
      intro k s h A
      have e1 : Sec.res (toOf A).g ((τ.deg s).app (Sq.of p A.u) (ev (R := R') α k s h (pullback p A.u) (pullback.fst p A.u))) =
          (τ.deg s).app A (Sec.res (toOf A).k (ev (R := R') α k s h (pullback p A.u) (pullback.fst p A.u))) :=
        (τ.deg s).nat (toOf A) _
      have e2 : Sec.res (toOf A).k (ev (R := R') α k s h (pullback p A.u) (pullback.fst p A.u)) =
          ev (R := R') α k s h A.V A.v := by
        refine (ev_res k s h (toOf A).k (pullback.fst p A.u)).trans ?_
        congr 1
        show (toOf A).k ≫ pullback.fst p A.u = A.v
        exact pullback.lift_fst _ _ _
      exact (hβ k s h A.U A.u).trans (((res_id _).symm.trans e1).trans (congrArg _ e2))
    refine ⟨β, hIm, fun β' h' => ev_ext β' β (fun k s h U u => ?_)⟩
    exact (h' k s h (Sq.of p u)).trans (hIm k s h (Sq.of p u)).symm
  · have ev_delta_zero {T : Type} [CommRing T] {E : Spc} {K : Cx T}
        (γ : Cochain ((chains T).obj E) K n) (U : Scheme.{0}) (x : Sx E 0 U) :
        ev (R := T) (δ n m γ) 0 m (by simp) U x =
          Sec.map (K.d n m) (ev (R := T) γ 0 n (by simp) U x) := by
      rw [ev_def, δ_v n m hm γ _ m (by simp) n 1 (by omega) (by simp),
        (CupSpec.isZero_chains E 1 one_pos).eq_of_tgt (((chains T).obj E).d _ 1) 0,
        zero_comp, smul_zero, add_zero]
      rfl
    have ev_delta_succ {T : Type} [CommRing T] {E : Spc} {K : Cx T}
        (γ : Cochain ((chains T).obj E) K n) (U : Scheme.{0}) (q : ℕ) (s t : ℤ)
        (hs : -((q + 1 : ℕ) : ℤ) + n = s) (ht : -((q + 1 : ℕ) : ℤ) + m = t)
        (x : Sx E (q + 1) U) :
        ev (R := T) (δ n m γ) (q + 1) t ht U x =
          Sec.map (K.d s t) (ev (R := T) γ (q + 1) s hs U x) +
            m.negOnePow • ∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) •
              ev (R := T) γ q t (by omega) U (x.face i) := by
      rw [ev_def, δ_v n m hm γ _ t ht s (-(q : ℤ)) (by omega) (by omega), Preadditive.comp_add,
        Units.smul_def, Preadditive.comp_zsmul, ← Category.assoc _ (((chains T).obj E).d _ _),
        CupSpec.chains_d, Category.assoc, Preadditive.sum_comp]
      refine (map_add (CupSpec.mapHom _ _ (freeGen T _ U x)) _ _).trans ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_zsmul, map_sum, Units.smul_def]
      refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
      rw [Preadditive.zsmul_comp, map_zsmul]
      congr 1
      change Sec.map ((chainsXIso T E q).inv ≫ γ.v _ _ _)
        (Sec.map ((free T).map _) (freeGen T _ U x)) = _
      rw [CupSpec.freeGen_map]
      rfl
    intro k s h A
    cases k with
    | zero =>
      have hs : s = m := by simpa using h.symm
      subst hs
      have eβ := ev_delta_zero (E := sch.obj S) β A.U A.u
      have eα := ev_delta_zero (E := sch.obj Z) α A.V A.v
      refine eβ.trans ?_
      refine Eq.trans ?_ (congrArg _ eα.symm)
      refine (congrArg _ (hαβ 0 n (by simp) A)).trans ?_
      exact τ.comm A n s _
    | succ q =>
      have eβ := ev_delta_succ (E := sch.obj S) β A.U q (-((q + 1 : ℕ) : ℤ) + n) s rfl h A.u
      have eα := ev_delta_succ (E := sch.obj Z) α A.V q (-((q + 1 : ℕ) : ℤ) + n) s rfl h A.v
      refine eβ.trans ?_
      refine Eq.trans ?_ (congrArg _ eα.symm)
      rw [map_add (f := _)]
      congr 1
      · exact (congrArg _ (hαβ _ _ rfl A)).trans (τ.comm A _ s _)
      · set_option synthInstance.maxHeartbeats 100000 in
          rw [Units.smul_def, Units.smul_def, map_zsmul, map_sum]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_zsmul]
        congr 1
        exact hαβ q s _ A
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PIndDesc
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces
open scoped TensorProduct

namespace UpperTheory.Gal.TranscendenceTraces

private noncomputable def pushIso (A B O : Type) [CommRing A] [CommRing B] [CommRing O] [Algebra A B] [Algebra A O] :
    (Under.pushout (CommRingCat.ofHom (algebraMap A B))).obj (Under.mk (CommRingCat.ofHom (algebraMap A O))) ≅
      Under.mk (CommRingCat.ofHom (algebraMap B (B ⊗[A] O))) :=
  Under.isoMk (CommRingCat.isPushout_tensorProduct A B O).flip.isoPushout.symm
    ((CommRingCat.isPushout_tensorProduct A B O).flip.inr_isoPushout_inv)

private def algOf {B C T : Type} [CommRing B] [CommRing C] [CommRing T] [Algebra B C] [Algebra B T]
    (f : Under.mk (CommRingCat.ofHom (algebraMap B C)) ⟶ Under.mk (CommRingCat.ofHom (algebraMap B T))) : C →ₐ[B] T :=
  { f.right.hom with
    commutes' := fun b => by
      have := congr($(Under.w f).hom b)
      simpa using this }

private def underOf {B C T : Type} [CommRing B] [CommRing C] [CommRing T] [Algebra B C] [Algebra B T]
    (f : C →ₐ[B] T) : Under.mk (CommRingCat.ofHom (algebraMap B C)) ⟶ Under.mk (CommRingCat.ofHom (algebraMap B T)) :=
  Under.homMk (CommRingCat.ofHom f.toRingHom) (by ext b; exact f.commutes b)

end UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.indDesc_of :
    IndDesc := by
  intro A O B C _ _ _ _ _ _ _ _ hO ⟨g⟩
  obtain ⟨J, _, _, D, ι, ⟨hc⟩, hD⟩ := GlobalTheory.T.exists_filtered_colimit_of_etale_of_indEt A O hO
  let F := Under.pushout (CommRingCat.ofHom (algebraMap A B))
  have hFc := isColimitOfPreserves F hc
  have : IsFinitelyPresentable.{0} (Under.mk (CommRingCat.ofHom (algebraMap B C))) :=
    CommRingCat.isFinitelyPresentable_under _ _
      (show (algebraMap B C).FinitePresentation from
        (RingHom.finitePresentation_algebraMap (A := B) (B := C)).mpr inferInstance)
  obtain ⟨j, q, -⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hFc
    (underOf g ≫ (pushIso A B O).inv)
  let E : Type := (D.obj j).right
  letI : Algebra A E := (D.obj j).hom.hom.toAlgebra
  refine ⟨E, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · exact RingHom.etale_algebraMap.mp (hD j)
  · refine ⟨{ (ι.app j).right.hom with commutes' := fun a => ?_ }⟩
    have := congr($(Under.w (ι.app j)).hom a)
    exact this
  · exact ⟨algOf (q ≫ (pushIso A B E).hom)⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PInvTrans
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

namespace UpperTheory.Gal.TranscendenceTraces

private theorem root_orbit {A B G Ω : Type} [CommRing A] [CommRing B] [Algebra A B] [Group G] [Finite G]
    [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G] [Field Ω] (φ ψ : B →+* Ω)
    (h : φ.comp (algebraMap A B) = ψ.comp (algebraMap A B)) (b : B) : ∃ g : G, ψ b = φ (g • b) :=
  _root_.UpperTheory.Reformulated.B.Qi49.root_orbit φ ψ h b

private theorem same_ker {A B G Ω : Type} [CommRing A] [CommRing B] [Algebra A B] [Group G] [Finite G]
    [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G] [Field Ω] (φ ψ : B →+* Ω)
    (h : φ.comp (algebraMap A B) = ψ.comp (algebraMap A B)) (hk : RingHom.ker φ = RingHom.ker ψ) :
    ∃ g : G, ∀ b, ψ b = φ (g • b) := by
  let Q : Ideal B := RingHom.ker φ
  haveI : Q.IsPrime := RingHom.ker_isPrime φ
  let P : Ideal A := Q.under A
  haveI : Q.LiesOver P := ⟨rfl⟩
  let φb : B ⧸ Q →+* Ω := Ideal.Quotient.lift Q φ (fun a ha => ha)
  let ψb : B ⧸ Q →+* Ω := Ideal.Quotient.lift Q ψ (fun a ha => by
    have : a ∈ RingHom.ker ψ := hk ▸ ha
    exact this)
  have φm : ∀ b, φb (Ideal.Quotient.mk Q b) = φ b := fun b => Ideal.Quotient.lift_mk _ _ _
  have ψm : ∀ b, ψb (Ideal.Quotient.mk Q b) = ψ b := fun b => Ideal.Quotient.lift_mk _ _ _
  have inj : ∀ f : B ⧸ Q →+* Ω, (∀ b, f (Ideal.Quotient.mk Q b) = 0 → b ∈ Q) → Function.Injective f := by
    intro f hf
    refine (injective_iff_map_eq_zero f).2 fun x hx => ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hf b hx)
  have φi : Function.Injective φb := inj φb fun b hb => by
    rw [φm] at hb
    exact hb
  have ψi : Function.Injective ψb := inj ψb fun b hb => by
    rw [ψm] at hb
    have h' : b ∈ RingHom.ker ψ := hb
    rw [← hk] at h'
    exact h'
  have hr : ψb.range = φb.range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨g, hg⟩ := root_orbit (G := G) φ ψ h b
      exact ⟨Ideal.Quotient.mk Q (g • b), by rw [φm, ψm, hg]⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨g, hg⟩ := root_orbit (G := G) ψ φ h.symm b
      exact ⟨Ideal.Quotient.mk Q (g • b), by rw [φm, ψm, hg]⟩
  let eφ : B ⧸ Q ≃+* φb.range := RingEquiv.ofBijective φb.rangeRestrict
    ⟨fun x y e => φi (congrArg Subtype.val e), φb.rangeRestrict_surjective⟩
  let eψ : B ⧸ Q ≃+* ψb.range := RingEquiv.ofBijective ψb.rangeRestrict
    ⟨fun x y e => ψi (congrArg Subtype.val e), ψb.rangeRestrict_surjective⟩
  let τ0 : B ⧸ Q ≃+* B ⧸ Q := (eψ.trans (RingEquiv.subringCongr hr)).trans eφ.symm
  have hτ : ∀ x, φb (τ0 x) = ψb x := by
    intro x
    have e : eφ (τ0 x) = RingEquiv.subringCongr hr (eψ x) := eφ.apply_symm_apply _
    exact congrArg Subtype.val e
  let τ : (B ⧸ Q) ≃ₐ[A ⧸ P] (B ⧸ Q) := AlgEquiv.ofRingEquiv (f := τ0) (fun a => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    apply φi
    rw [hτ]
    change ψb (Ideal.Quotient.mk Q (algebraMap A B a)) = φb (Ideal.Quotient.mk Q (algebraMap A B a))
    rw [φm, ψm]
    exact (congrArg (fun f => f a) h).symm)
  obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective G P Q τ
  refine ⟨g.1, fun b => ?_⟩
  have e1 : Ideal.Quotient.stabilizerHom Q P G g (Ideal.Quotient.mk Q b) = Ideal.Quotient.mk Q (g.1 • b) :=
    Ideal.Quotient.stabilizerHom_apply Q P G g b
  rw [hg] at e1
  have e2 := hτ (Ideal.Quotient.mk Q b)
  rw [ψm] at e2
  rw [← e2, ← φm]
  exact congrArg φb e1

end UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.invTrans_of :
    InvTrans := by
  intro A B G Ω _ _ _ _ _ _ _ _ _ φ φ' h
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  haveI : (RingHom.ker φ').IsPrime := RingHom.ker_isPrime φ'
  have hu : (RingHom.ker φ).under A = (RingHom.ker φ').under A := by
    ext a
    change φ (algebraMap A B a) = 0 ↔ φ' (algebraMap A B a) = 0
    rw [show φ (algebraMap A B a) = φ' (algebraMap A B a) from congrArg (fun f => f a) h]
  obtain ⟨g0, hg0⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B G _ _ hu
  let ψ : B →+* Ω := φ'.comp (MulSemiringAction.toRingHom G B g0)
  have hψ : ∀ b, ψ b = φ' (g0 • b) := fun _ => rfl
  have hk : RingHom.ker φ = RingHom.ker ψ := by
    ext b
    have e : g0 • b ∈ RingHom.ker φ' ↔ b ∈ RingHom.ker φ := by
      rw [hg0]
      exact Ideal.smul_mem_pointwise_smul_iff
    rw [← e, RingHom.mem_ker, RingHom.mem_ker, hψ]
  have hA : φ.comp (algebraMap A B) = ψ.comp (algebraMap A B) := by
    ext a
    have e : φ (algebraMap A B a) = φ' (algebraMap A B a) := congrArg (fun f => f a) h
    simp [hψ, e, smul_algebraMap]
  obtain ⟨g, hg⟩ := same_ker (G := G) φ ψ hA hk
  refine ⟨g * g0⁻¹, fun b => ?_⟩
  have e := hg (g0⁻¹ • b)
  rw [hψ, smul_inv_smul, ← mul_smul] at e
  exact e
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PIsolate
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.isolate_of :
    Chart → IsolateSpec → Isolate := by
  intro hC hI Z S p _ z
  have hmem : p z ∈ (⊤ : S.Opens) := trivial
  obtain ⟨U, hU0, hzU, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens) hmem
  have hU : IsAffineOpen U := hU0
  let u0 : Spec (CommRingCat.of Γ(S, U)) ⟶ S := hU.isoSpec.inv ≫ Scheme.Opens.ι U
  obtain ⟨B, iB, iAB, v0, hfin, hpb⟩ := hC p Γ(S, U) u0
  haveI := hfin
  obtain ⟨y, hy⟩ : ∃ y : (U : Scheme), Scheme.Opens.ι U y = p z := ⟨⟨p z, hzU⟩, rfl⟩
  have ha : u0 (hU.isoSpec.hom y) = p z := by
    show (hU.isoSpec.hom ≫ hU.isoSpec.inv ≫ Scheme.Opens.ι U) y = p z
    rw [Iso.hom_inv_id_assoc, hy]
  obtain ⟨w0, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := u0) z _ ha.symm
  have hw : v0 (hpb.isoPullback.inv w0) = z := by
    rw [← Scheme.Hom.comp_apply, hpb.isoPullback_inv_fst, hw1]
  obtain ⟨A', W, v, hEt, hW, hvW, hvv, hiso⟩ := hI Γ(S, U) B (hpb.isoPullback.inv w0)
  haveI := hEt
  refine ⟨⟨A'.U, A'.V, A'.u ≫ u0, A'.v ≫ v0, A'.r, A'.pb.paste_horiz hpb⟩, W, v, ?_, hW, hvW, ?_, hiso⟩
  · show Etale (A'.u ≫ u0)
    infer_instance
  · show (A'.v ≫ v0) v = z
    rw [Scheme.Hom.comp_apply, hvv, hw]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PIsolateSpec
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.isolateSpec_of :
    IsolateSpec := by
  intro R B _ _ _ _ z
  let z' : PrimeSpectrum B := z
  haveI : z'.asIdeal.IsPrime := z'.isPrime
  haveI : Algebra.QuasiFiniteAt R z'.asIdeal := inferInstance
  obtain ⟨R', _, _, hEt, P, _, _, e, he, P', hP', hlo, hq, heP, -, -, huniq⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq (z'.asIdeal.under R) z'.asIdeal
  have pb := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R R' B)).flip
  refine ⟨⟨Spec (CommRingCat.of R'), Spec (CommRingCat.of (TensorProduct R R' B)), _, _, _, pb⟩,
    ((PrimeSpectrum.basicOpen e : TopologicalSpace.Opens (PrimeSpectrum (TensorProduct R R' B))) :
      Set (PrimeSpectrum (TensorProduct R R' B))),
    (⟨P', hP'⟩ : PrimeSpectrum (TensorProduct R R' B)), ?_, ?_, ?_, ?_, ?_⟩
  · exact HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hEt)
  · exact PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
  · exact heP
  · apply PrimeSpectrum.ext
    exact hq
  · intro v' hv' hr
    have h1 : (v' : PrimeSpectrum (TensorProduct R R' B)).asIdeal.LiesOver P := by
      constructor
      have h2 : Ideal.comap (algebraMap R' (TensorProduct R R' B))
          (v' : PrimeSpectrum (TensorProduct R R' B)).asIdeal =
          Ideal.comap (algebraMap R' (TensorProduct R R' B)) P' :=
        congrArg PrimeSpectrum.asIdeal hr
      rw [Ideal.under, h2]
      exact hlo.over
    apply PrimeSpectrum.ext
    exact huniq _ (PrimeSpectrum.isPrime _) h1 hv'
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PLocFinAff
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces
open scoped TensorProduct

theorem UpperTheory.Gal.TranscendenceTraces.locFinAff_of :
    Chart → RingSplit → LocFinAff := by
  intro hC hR W V U _ π r _ _ _ x
  let A := Γ(U, ⊤)
  let u : Spec (CommRingCat.of A) ⟶ U := U.isoSpec.inv
  obtain ⟨B, _, _, v, _, hpb⟩ := hC r A u
  haveI : IsIso v := hpb.isIso_fst_of_isIso
  let f : W ⟶ Spec (CommRingCat.of B) := π ≫ inv v
  obtain ⟨C, g, h, hg, hh⟩ := GlobalTheory.T.exists_etaleFaithfullyFlat_refining_etale_surjection (CommRingCat.of B) W f inferInstance inferInstance
  letI : Algebra B C := g.hom.toAlgebra
  haveI : Algebra.Etale B C := hg.1
  haveI : Module.FaithfullyFlat B C := hg.2
  let P : PrimeSpectrum A := U.isoSpec.hom x
  obtain ⟨E, _, _, hE, ⟨Q, hQ⟩, ⟨φ⟩⟩ := hR A B C P
  let gE : Spec (CommRingCat.of E) ⟶ U := Spec.map (CommRingCat.ofHom (algebraMap A E)) ≫ u
  haveI : Etale (Spec.map (CommRingCat.ofHom (algebraMap A E))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hE)
  have big := (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A B E)).paste_horiz hpb
  have hhπ : h ≫ π = Spec.map g ≫ v := by
    rw [← hh]
    simp [f]
  refine ⟨Spec (CommRingCat.of E), gE, inferInstance, inferInstance, ⟨Q, ?_⟩, ?_⟩
  · change u (Spec.map (CommRingCat.ofHom (algebraMap A E)) Q) = x
    have e : Spec.map (CommRingCat.ofHom (algebraMap A E)) Q = P := hQ
    rw [e]
    show U.isoSpec.inv (U.isoSpec.hom x) = x
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  · refine ⟨big.lift (pullback.fst r gE) (pullback.snd r gE) pullback.condition ≫
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ h, ?_⟩
    have eφ : g ≫ CommRingCat.ofHom φ.toRingHom = CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom := by
      ext b
      exact φ.commutes b
    rw [Category.assoc, Category.assoc, hhπ, ← Category.assoc (Spec.map _) (Spec.map g) v, ← Spec.map_comp, eφ]
    exact big.lift_fst _ _ _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PLocFinGeo
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.locFinGeo_of :
    LocFinAff → LocFinGeo := by
  intro hA W V U π r _ _ _
  rw [GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover U (fun V' g ↦ ∃ s, s ≫ π = pullback.fst r g)]
  swap
  · rintro V' W' g k ⟨s, hs⟩
    refine ⟨pullback.lift (pullback.fst r (k ≫ g)) (pullback.snd r (k ≫ g) ≫ k)
      (by simp [pullback.condition]) ≫ s, ?_⟩
    rw [Category.assoc, hs, pullback.lift_fst]
  intro x
  obtain ⟨y, hy⟩ := U.affineCover.covers x
  set ι := U.affineCover.f (U.affineCover.idx x) with hι
  obtain ⟨U', g, hU', hg, ⟨z, hz⟩, s, hs⟩ :=
    hA (pullback.snd π (pullback.fst r ι)) (pullback.snd r ι) y
  refine ⟨U', g ≫ ι, hU', inferInstance, ⟨z, by simp [hz, hy]⟩, ?_⟩
  let φ : pullback r (g ≫ ι) ⟶ pullback (pullback.snd r ι) g :=
    pullback.lift (pullback.lift (pullback.fst r (g ≫ ι)) (pullback.snd r (g ≫ ι) ≫ g)
      (by rw [Category.assoc, ← pullback.condition]))
      (pullback.snd r (g ≫ ι)) (pullback.lift_snd _ _ _)
  refine ⟨φ ≫ s ≫ pullback.fst π (pullback.fst r ι), ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc s, hs]
  dsimp only [φ]
  rw [← Category.assoc, pullback.lift_fst, pullback.lift_fst]
end

