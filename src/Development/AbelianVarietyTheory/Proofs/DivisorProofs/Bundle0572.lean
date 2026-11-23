module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0399
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0517
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0459
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0437
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSheafComplexPairingTensorAssocDesc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCocycleFirstChernClassTateTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSuppSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCoefficientReductionCup
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedCup

theorem sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  simp only [Sec.res, Sec.map]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

theorem sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem cpush_id {R : Type} [CommRing R] (K I : Cx R) (n : ℤ) (a : CohomologyClass K I n) : cpush K (𝟙 I) n a = a := by
  obtain ⟨a, rfl⟩ := a.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

def semiPre {S R : Type} [CommRing S] [CommRing R] {T K : Cx S} {K' : Cx R} (u : T ⟶ K) (ρ : SemiMap K K') :
    SemiMap T K' where
  app U s := (ρ.app U s).comp ((u.f s).hom.app (op U)).hom.toAddMonoidHom
  nat g s a := by
    change Sec.res g (ρ.app _ s (Sec.map (u.f s) a)) = ρ.app _ s (Sec.map (u.f s) (Sec.res g a))
    rw [ρ.nat, sec_map_res]
  comm U s t a := by
    change Sec.map (_ : _ ⟶ _) (ρ.app U s (Sec.map (u.f s) a)) = ρ.app U t (Sec.map (u.f t) (Sec.map (T.d s t) a))
    rw [ρ.comm, ← sec_map_comp, ← sec_map_comp, u.comm]

theorem ev_comp_ofHom {R : Type} [CommRing R] {E : Spc} {I K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (u : I ⟶ K)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (R := R) (α.comp (Cochain.ofHom u) (add_zero n)) p s h U x =
      Sec.map (u.f s) (ev (R := R) α p s h U x) := by
  simp only [ev, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rfl

theorem semiPre_op {S R : Type} [CommRing S] [CommRing R] {T K : Cx S} {K' : Cx R} (u : T ⟶ K) (ρ : SemiMap K K')
    (E : Spc) (n : ℤ) (x : CohomologyClass ((chains S).obj E) T n) :
    (semiPre u ρ).op.app E n x = ρ.op.app E n (cpush _ u n x) := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ).1 E n (zcomp α (Cocycle.ofHom u) (add_zero n))
  change _ = ρ.op.app E n (CohomologyClass.mk (zcomp α (Cocycle.ofHom u) (add_zero n)))
  rw [(GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ).2 E n _ β hβ]
  refine (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R (semiPre u ρ)).2 E n α β (fun p s h U y => ?_)
  rw [hβ p s h U y]
  change ρ.app U s (ev (R := S) (α.1.comp (Cochain.ofHom u) (add_zero n)) p s h U y) = _
  rw [ev_comp_ofHom]
  rfl

theorem semiMap_cup : ∀ (S R : Type) [CommRing S] [CommRing R] {I J T : Cx S} {I' J' K' : Cx R} (τ : Pair I J T) (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J') (σ : SemiMap T K'), (∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U), σ.app U w (τ.mul U s t w h a b) = ν.mul U s t w h (ρ₁.app U s a) (ρ₂.app U t b)) → ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) (a : CohomologyClass ((chains S).obj E) I n) (b : CohomologyClass ((chains S).obj E) J m), σ.op.app E k (τ.cup E hk a b) = ν.cup E hk (ρ₁.op.app E n a) (ρ₂.op.app E m b) := by
  intro S R _ _ I J T I' J' K' τ ν ρ₁ ρ₂ σ hσ E n m k hk a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW S τ hk).1 α β
  obtain ⟨α', hα'⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ₁).1 E n α
  obtain ⟨β', hβ'⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ₂).1 E m β
  obtain ⟨γ', hγ'⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R σ).1 E k γ
  rw [(GlobalTheory.T.cup_eq_class_of_isAW S τ hk).2 α β γ hγ, (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R σ).2 E k γ γ' hγ',
    (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ₁).2 E n α α' hα', (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ₂).2 E m β β' hβ']
  refine ((GlobalTheory.T.cup_eq_class_of_isAW R ν hk).2 α' β' γ' ?_).symm
  intro N w h U x
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hγ' N w h U x, hγ N w h U x, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Units.smul_def, map_zsmul, hσ, ← hα', ← hβ', Units.smul_def]

theorem reduction_cup : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (E : Spc) {n m i j : ℤ} (a : Ht Q E n i) (b : Ht Q E m j),
    red Q q E _ _ (cup Q a b) = cup q (red Q q E _ _ a) (red Q q E _ _ b) := by
  intro Q q _ hqQ E n m i j a b
  haveI : NeZero q := ⟨by rintro rfl; exact NeZero.ne Q (zero_dvd_iff.mp hqQ)⟩
  obtain ⟨T, τ, hτ⟩ := GlobalTheory.T.exists_isTensor_etaleSheafComplexPairing (ZMod Q) (res _ (tw Q i)) (res _ (tw Q j))
  obtain ⟨u, hu, -⟩ := (GlobalTheory.T.isTensor_universal_property (ZMod Q) τ hτ).1 (twPair Q i j) (𝟙 _) (𝟙 _)
  have hcup : cup Q a b = cpush _ u _ (τ.cup E rfl a b) := by
    rw [GlobalTheory.T.cupProduct_natural_in_sheafComplexPairing (ZMod Q) τ (twPair Q i j) (𝟙 _) (𝟙 _) u hu E rfl a b, cpush_id, cpush_id]
    rfl
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_semiMap_of_tensorPairing Q (ZMod q) τ hτ (twPair q i j) (redMap Q q i) (redMap Q q j)
  have h1 := semiMap_cup (ZMod Q) (ZMod q) τ (twPair q i j) (redMap Q q i) (redMap Q q j) σ hσ E rfl a b
  rw [hcup]
  change (redMap Q q (i + j)).op.app E (n + m) (cpush _ u _ _) = (twPair q i j).cup E rfl _ _
  rw [← semiPre_op]
  change _ = (twPair q i j).cup E rfl ((redMap Q q i).op.app E n a) ((redMap Q q j).op.app E m b)
  rw [← h1]
  have hres := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy Q i
  have hresj := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy Q j
  have htw := GlobalTheory.T.isTateTwistResolution_tensor_flat Q i j (i + j) rfl (fun _ ζ => resGen i ζ) (fun _ ζ => resGen j ζ) hres.1 hresj.1 hresj.2.1 τ hτ
  have hflat := GlobalTheory.T.flat_tensor_of_flat_complexes (ZMod Q) τ hτ hres.2.1 hresj.2.1
  refine GlobalTheory.T.semiMap_eq_of_flat_tateTwist_resolution Q q hqQ (i + j) _ htw hflat _ _ ?_ E (n + m) _
  intro U ζ
  obtain ⟨ξ, hξ⟩ := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties Q Γ(U, ⊤)).2.2.2.2.2 q hqQ ζ
  rw [hσ, GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ i U ζ ξ hξ, GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ j U ζ ξ hξ, (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q i j).1 U ξ]
  change (redMap Q q (i + j)).app U 0 (Sec.map (u.f 0) _) = _
  rw [hu]
  change (redMap Q q (i + j)).app U 0 ((twPair Q i j).mul U 0 0 0 _ (resGen i ζ) (resGen j ζ)) = _
  rw [(GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique Q i j).1 U ζ, GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ (i + j) U ζ ξ hξ]

end GlobalTheory.EtC.RedCup

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductAssoc
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.CupAssoc

def trPair {q : ℕ} {I J : Cx (ZMod q)} {k k' : ℤ} (h : k = k') (μ : Pair I J (res _ (tw q k))) :
    Pair I J (res _ (tw q k')) := h ▸ μ

theorem trPair_isTwPair {q : ℕ} {i j k k' : ℤ} (h : k = k') (μ : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k)))
    (hμ : IsTwPair μ) : IsTwPair (trPair h μ) := by
  subst h; exact hμ

theorem trPair_cup {q : ℕ} {I J : Cx (ZMod q)} {k k' : ℤ} (h : k = k') (μ : Pair I J (res _ (tw q k))) (E : Spc)
    {n m w : ℤ} (hw : n + m = w) (a : CohomologyClass ((chains _).obj E) I n) (b : CohomologyClass ((chains _).obj E) J m) :
    (trPair h μ).cup E hw a b = Ht.cast hw h (μ.cup E rfl a b) := by
  subst h; subst hw; rfl

theorem secMap_id {R : Type} [CommRing R] (K : Cx R) (s : ℤ) {U : Scheme.{0}} (x : Sec (K.X s) U) :
    Sec.map (HomologicalComplex.Hom.f (𝟙 K) s) x = x := rfl

theorem main : ∀ (q : ℕ) [NeZero q] (E : Spc) {n m k i j l : ℤ} (a : Ht q E n i) (b : Ht q E m j) (c : Ht q E k l),
    cup q (cup q a b) c = (cup q a (cup q b c)).cast (by ring) (by ring) := by
  intro q _ E n m k i j l a b c
  have hk : i + (j + l) = i + j + l := by ring
  have hd : n + (m + k) = n + m + k := by ring

  set μ := twPair q i j with hμdef
  set P := twPair q (i + j) l with hPdef
  set μ' := twPair q j l with hμ'def
  set Q' := trPair hk (twPair q i (j + l)) with hQ'def
  have hμ : IsTwPair μ := (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q i j).1
  have hP : IsTwPair P := (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q (i + j) l).1
  have hμ' : IsTwPair μ' := (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q j l).1
  have hQ' : IsTwPair Q' := trPair_isTwPair hk _ (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q i (j + l)).1
  have hfun := GlobalTheory.EtC.ZcFun.main (ZMod q)
  have cpush_id : ∀ (K I : Cx (ZMod q)) (n : ℤ) x, cpush K (𝟙 I) n x = x := fun K I n x => ((hfun.1 K I n x).2)

  obtain ⟨hIi, hFi, -⟩ := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q i
  obtain ⟨hIj, hFj, -⟩ := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q j
  obtain ⟨hIl, hFl, -⟩ := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q l
  obtain ⟨-, -, hext⟩ := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q (i + j + l)
  obtain ⟨T, τ, hτ⟩ := GlobalTheory.T.exists_isTensor_etaleSheafComplexPairing (ZMod q) (res _ (tw q i)) (res _ (tw q j))
  obtain ⟨T3, τ', hτ'⟩ := GlobalTheory.T.exists_isTensor_etaleSheafComplexPairing (ZMod q) T (res _ (tw q l))
  have hT := GlobalTheory.T.isTateTwistResolution_tensor_flat q i j (i + j) rfl _ _ hIi hIj hFj τ hτ
  have hT3 := GlobalTheory.T.isTateTwistResolution_tensor_flat q (i + j) l (i + j + l) rfl _ _ hT hIl hFl τ' hτ'

  obtain ⟨u, hu, -⟩ := (GlobalTheory.T.isTensor_universal_property (ZMod q) τ hτ).1 μ (𝟙 _) (𝟙 _)
  obtain ⟨u₁, hu₁, -⟩ := (GlobalTheory.T.isTensor_universal_property (ZMod q) τ' hτ').1 P u (𝟙 _)
  have L1 : μ.cup E rfl a b = cpush _ u (n + m) (τ.cup E rfl a b) := by
    rw [GlobalTheory.T.cupProduct_natural_in_sheafComplexPairing (ZMod q) τ μ (𝟙 _) (𝟙 _) u hu E rfl a b, cpush_id, cpush_id]
  have L2 : P.cup E rfl (cpush _ u (n + m) (τ.cup E rfl a b)) c = cpush _ u₁ (n + m + k) (τ'.cup E rfl (τ.cup E rfl a b) c) := by
    rw [GlobalTheory.T.cupProduct_natural_in_sheafComplexPairing (ZMod q) τ' P u (𝟙 _) u₁ hu₁ E rfl _ c, cpush_id]

  obtain ⟨ν, hν⟩ := _root_.GlobalTheory.EtC.tensor_assoc_desc (ZMod q) τ τ' hτ hτ' μ' Q'
  obtain ⟨u₂, hu₂, -⟩ := (GlobalTheory.T.isTensor_universal_property (ZMod q) τ' hτ').1 ν (𝟙 _) (𝟙 _)
  have R1 : ν.cup E rfl (τ.cup E rfl a b) c = Q'.cup E hd a (μ'.cup E rfl b c) :=
    _root_.GlobalTheory.EtC.Pair.cup_assoc_of_mul_assoc (ZMod q) τ ν μ' Q' hν E rfl rfl rfl hd a b c
  have R2 : cpush _ u₂ (n + m + k) (τ'.cup E rfl (τ.cup E rfl a b) c) = ν.cup E rfl (τ.cup E rfl a b) c := by
    rw [GlobalTheory.T.cupProduct_natural_in_sheafComplexPairing (ZMod q) τ' ν (𝟙 _) (𝟙 _) u₂ hu₂ E rfl _ c, cpush_id, cpush_id]

  have hgen : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map (u₁.f 0) (τ'.mul U 0 0 0 (add_zero 0) (τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)) (resGen l ζ)) =
      Sec.map (u₂.f 0) (τ'.mul U 0 0 0 (add_zero 0) (τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)) (resGen l ζ)) := by
    intro U ζ
    rw [hu₁, hu₂]
    try simp only [secMap_id]
    rw [hu]
    try simp only [secMap_id]
    rw [hμ U ζ, hP U ζ, hν U 0 0 0 0 0 0 (add_zero 0) (add_zero 0) (add_zero 0) (add_zero 0), hμ' U ζ, hQ' U ζ]
  obtain ⟨hH⟩ := (hext _ hT3).2 u₁ u₂ hgen
  have hpush := ((hfun.2.2.2.2 u₁ u₂ ⟨hH⟩) ((chains _).obj E) (n + m + k)).2

  show P.cup E rfl (μ.cup E rfl a b) c = _
  rw [L1, L2, hpush, R2, R1, hQ'def, trPair_cup]
  rfl

end GlobalTheory.EtC.CupAssoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductGradedComm
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem cup_eq_cast_of_isTwPair (q : ℕ) [NeZero q] (E : Spc) {n m i j k w : ℤ} (hk : i + j = k) (hw : n + m = w)
    (ν : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k))) (hν : IsTwPair ν) (a : Ht q E n i) (b : Ht q E m j) :
    ν.cup E hw a b = (cup q a b).cast hw hk := by
  subst hk
  subst hw
  have h := (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q i j).2 (i + j) rfl ν (twPair q i j) hν (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q i j).1 E (n := n) (m := m) rfl
  rw [h]
  rfl

theorem isTwPair_of_isFlip (q : ℕ) {i j k : ℤ} (μ : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k)))
    (ν : Pair (res _ (tw q j)) (res _ (tw q i)) (res _ (tw q k))) (hμ : IsTwPair μ) (h : μ.IsFlip ν) : IsTwPair ν := by
  intro U ζ
  rw [h U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ), hμ U ζ]
  simp

theorem cup_comm (q : ℕ) [NeZero q] (E : Spc) {n m i j : ℤ} (a : Ht q E n i) (b : Ht q E m j) :
    cup q a b = (n * m).negOnePow • (cup q b a).cast (by ring) (by ring) := by
  obtain ⟨ν, hf, -, -⟩ := GlobalTheory.T.exists_isFlip_sheafComplexPairing (ZMod q) (twPair q i j)
  have hν : IsTwPair ν := isTwPair_of_isFlip q _ ν (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q i j).1 hf
  have h1 := _root_.GlobalTheory.EtC.Pair.cup_flip (ZMod q) (twPair q i j) ν hf E (n := n) (m := m) (k := n + m) rfl (by ring) a b
  have h2 := cup_eq_cast_of_isTwPair q E (n := m) (m := n) (i := j) (j := i) (k := i + j) (w := n + m) (by ring) (by ring) ν hν b a
  change (twPair q i j).cup E rfl a b = _
  rw [h1, h2]

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupUnitAndPrimitiveRootClasses
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.CupGen
open ClsSpec

theorem sub_zero_full {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (h : 0 + N ≤ N) : x.sub 0 N h = x := by
  have : SimplexCategory.subinterval 0 N h = 𝟙 _ := by
    ext i; simp [SimplexCategory.subinterval]
  simp [Sx.sub, this]

theorem aw_zero_left {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {m : ℤ} (hm : 0 + m = m)
    (hI : ∀ (s : ℤ) (U : Scheme.{0}), s < 0 → Subsingleton (Sec (I.X s) U))
    (α : Cochain ((chains R).obj E) I 0) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K m)
    (h : μ.IsAW hm α β γ) (N : ℕ) (w : ℤ) (hw : -(N : ℤ) + m = w) (U : Scheme.{0}) (x : Sx E N U) :
    ev γ N w hw U x = μ.mul U 0 w w (zero_add w) (ev α 0 0 (by simp) U (x.sub 0 0 (by omega))) (ev β N w hw U x) := by
  rw [h N w hw U x, Finset.sum_eq_single 0]
  · subst hw
    have e1 : ((m * (((0 : Fin (N + 1)) : ℕ) : ℤ)).negOnePow) = 1 := by simp
    rw [e1, one_smul]
    have e2 : x.sub ((0 : Fin (N + 1)) : ℕ) (N - ((0 : Fin (N + 1)) : ℕ)) (by simp) = x := sub_zero_full x (by omega)
    rw [e2]
    rfl
  · intro p _ hp
    have hp' : 0 < (p : ℕ) := Fin.pos_iff_ne_zero.2 hp
    haveI := hI (-((p : ℕ) : ℤ) + 0) U (by omega)
    rw [Subsingleton.elim (ev α p _ rfl U _) 0, map_zero, LinearMap.zero_apply, smul_zero]
  · intro h0; exact absurd (Finset.mem_univ _) h0

theorem factor_cochain {R : Type} [CommRing R] {E : Spc} {D C : Cx R} (ι : D ⟶ C)
    (hinj : ∀ n U, Function.Injective (Sec.map (ι.f n) (U := U))) {n : ℤ} (β : Cochain ((chains R).obj E) C n)
    (hβ : ∀ p s h U x, ∃ b, Sec.map (ι.f s) b = ev β p s h U x) :
    ∃ β' : Cochain ((chains R).obj E) D n, β'.comp (Cochain.ofHom ι) (add_zero n) = β := by
  choose b hb using hβ
  obtain ⟨β', hβ'⟩ := GlobalTheory.T.exists_cochain_ev_eq_of_natural' R (E := E) (I := D) (n := n) b (fun p s h V U g x => by
    apply hinj
    rw [← res_map, hb, hb, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.1])
  refine ⟨β', (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.1 _ _ fun p s h U x => ?_⟩
  rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.2.2, hβ', hb]

theorem supp_twres (q : ℕ) [NeZero q] (i : ℤ) (D : Cx (ZMod q)) (ι : D ⟶ res _ (tw q i))
    (hinj : ∀ n U, Function.Injective (Sec.map (ι.f n) (U := U)))
    (hD : ∀ n U (a : Sec ((res _ (tw q i)).X n) U), (∃ b, Sec.map (ι.f n) b = a) ↔
      Loc U fun V g => IsUnit (q : Γ(V, ⊤)) ∨ Sec.res g a = 0) :
    ∃ e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (D.X 0) U, IsTwRes q i D e ∧
      ∀ U ζ, Sec.map (ι.f 0) (e U ζ) = resGen i ζ := GlobalTheory.T.supportedSections_tateTwist_resolution q i D ι hinj hD

theorem exists_unit_map (q : ℕ) [NeZero q] (i k : ℤ) (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q k)))
    (D : Cx (ZMod q)) (ι : D ⟶ res _ (tw q i))
    (hD : ∀ n U (a : Sec ((res _ (tw q i)).X n) U), (∃ b, Sec.map (ι.f n) b = a) ↔
      Loc U fun V g => IsUnit (q : Γ(V, ⊤)) ∨ Sec.res g a = 0) :
    ∃ u : D ⟶ res _ (tw q k), ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (s : ℤ) (b : Sec (D.X s) U),
      Sec.map (u.f s) b = μ.mul U 0 s s (zero_add s) (resGen 0 ζ) (Sec.map (ι.f s) b) := GlobalTheory.T.unitSection_multiplication_chainMap q i k μ D ι hD

theorem loc_all {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => h V g⟩

theorem root_mul (q : ℕ) [NeZero q] (X : Scheme.{0}) (ζ : Prim q Γ(X, ⊤)) (i j : ℤ) :
    cup q (rootClass i ζ) (rootClass j ζ) = (rootClass (i + j) ζ).cast (by ring) rfl ∧
      rootClass 0 ζ = one q (sch.obj X) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨α, hα, hαv⟩ := rootClass_spec i ζ
    obtain ⟨β, hβ, hβv⟩ := rootClass_spec j ζ
    obtain ⟨γ, hγ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW (ZMod q) (twPair q i j) (E := sch.obj X) (rfl : (0 : ℤ) + 0 = 0 + 0)).1 α β
    have hc := (GlobalTheory.T.cup_eq_class_of_isAW (ZMod q) (twPair q i j) (E := sch.obj X) (rfl : (0 : ℤ) + 0 = 0 + 0)).2 α β γ hγ
    change (twPair q i j).cup (sch.obj X) rfl (rootClass i ζ) (rootClass j ζ) = rootClass (i + j) ζ
    rw [← hα, ← hβ, hc, (GlobalTheory.T.tateTwistUnitClass_rootClass_spec q).2.2.2]
    refine ((GlobalTheory.T.degreeZeroSectionClass_properties (ZMod q) (tw q (i + j)) X).1 _ γ).1 ?_
    have e := hγ 0 0 (by simp) X (𝟙 X)
    rw [Finset.sum_eq_single 0 (fun p _ hp => absurd (Subsingleton.elim (α := Fin 1) p 0) hp) (fun h0 => absurd (Finset.mem_univ _) h0)] at e
    have e1 : (((0 : ℤ) * (((0 : Fin 1) : ℕ) : ℤ)).negOnePow) = 1 := by simp
    rw [e1, one_smul] at e
    refine e.trans ?_
    have a1 := hαv X (𝟙 X)
    have b1 := hβv X (𝟙 X)
    rw [res_id] at a1 b1
    change (twPair q i j).mul X 0 0 0 (add_zero 0) (ev α.1 0 0 (by simp) X (𝟙 X)) (ev β.1 0 0 (by simp) X (𝟙 X)) = _
    rw [a1, b1]
    exact (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q i j).1 X ζ
  · obtain ⟨α, hα, hαv⟩ := rootClass_spec 0 ζ
    have hE : Inv q (sch.obj X) := fun U ⟨x⟩ => unit_res (x : U ⟶ X) ζ.2.1
    rw [← hα]
    refine (GlobalTheory.T.tateTwistUnitClass_rootClass_spec q).2.1 _ hE α fun U x ξ => ?_
    refine (hαv U x).trans ?_
    exact (res_resGen (q := q) 0 (show U ⟶ X from x) ζ).trans (resGen_zero_eq _ _)

theorem one_mul_of_pair (q : ℕ) [NeZero q] (E : Spc) (hE : Inv q E) (n i : ℤ) (hn : 0 + n = n)
    (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q i))) (hμ : IsTwPair μ) (a : Ht q E n i) :
    μ.cup E hn (one q E) a = a := by
  obtain ⟨α, hα1, hαv⟩ := (GlobalTheory.T.tateTwistUnitClass_rootClass_spec q).1 E hE
  obtain ⟨β, rfl⟩ := a.mk_surjective
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW (ZMod q) μ hn).1 α β
  rw [← hα1, (GlobalTheory.T.cup_eq_class_of_isAW (ZMod q) μ hn).2 α β γ hγ]
  obtain ⟨D, ι, hinj, hD⟩ := GlobalTheory.EtC.SuppSub.exists_supp_sub (ZMod q) (res _ (tw q i))
    (fun U => IsUnit (q : Γ(U, ⊤))) (fun V U g h => unit_res g h)
  obtain ⟨e, he, heι⟩ := supp_twres q i D ι hinj hD
  obtain ⟨u, hu⟩ := exists_unit_map q i i μ D ι hD
  have hom : Nonempty (Homotopy u ι) := ((GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q i).2.2 e he).2 u ι fun U ζ => by
    rw [hu U ζ 0 (e U ζ), heι]
    exact hμ U ζ

  have hunit : ∀ (p : ℕ) (U : Scheme.{0}) (x : Sx E p U), IsUnit (q : Γ(U, ⊤)) :=
    fun p U x => hE U ⟨x.sub 0 0 (by omega)⟩
  obtain ⟨β', hβ'⟩ := factor_cochain ι hinj β.1 fun p s h U x =>
    (hD s U _).2 (loc_all fun V g => Or.inl (unit_res g (hunit p U x)))
  have hδ : δ n (n + 1) β' = 0 := by
    refine (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 _ _ fun p s h U x => hinj s U ?_
    rw [← (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.2, ← δ_comp_ofHom, hβ', Cocycle.δ_eq_zero, ev_zero, ev_zero, smap_zero]
  set β'' : Cocycle ((chains (ZMod q)).obj E) D n := Cocycle.mk β' (n + 1) rfl hδ
  have hb : CohomologyClass.mk β = cpush _ ι n (CohomologyClass.mk β'') := by
    change _ = CohomologyClass.mk _
    congr 1
    exact Cocycle.ext hβ'.symm
  have hg : CohomologyClass.mk γ = cpush _ u n (CohomologyClass.mk β'') := by
    change _ = CohomologyClass.mk _
    congr 1
    refine Cocycle.ext ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 _ _ fun N w hw U x => ?_)
    change ev γ.1 N w hw U x = ev (β'.comp (Cochain.ofHom u) (add_zero n)) N w hw U x
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.2, aw_zero_left μ hn (fun s U hs => (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness (ZMod q) (tw q 0) U).2.2.2 s hs)
      α.1 β.1 γ.1 hγ N w hw U x]
    refine ClsSpec.sep (ClsSpec.loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).1 (hunit N U x)) fun V g hz => ?_)
    obtain ⟨ζ⟩ := hz
    rw [res_map, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 β', hu V ζ w, ← hβ', (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.2,
      μ.nat g, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 α.1, res_map, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 β', hαv V _ ζ]
  rw [hb, hg, ((GlobalTheory.EtC.ZcFun.main (ZMod q)).2.2.2.2 u ι hom _ n).2]

theorem main : ∀ (q : ℕ) [NeZero q], (∀ E : Spc, Inv q E → ∀ {n i : ℤ} (a : Ht q E n i), cup q (one q E) a = a.cast (by ring) (by ring)) ∧ (∀ (X : Scheme.{0}) (ζ : Prim q Γ(X, ⊤)) (i j : ℤ), cup q (rootClass i ζ) (rootClass j ζ) = (rootClass (i + j) ζ).cast (by ring) rfl ∧ rootClass 0 ζ = one q (sch.obj X)) := by
  intro q _
  refine ⟨fun E hE => ?_, fun X ζ i j => root_mul q X ζ i j⟩
  intro n i a
  have key : ∀ (k : ℤ) (hk : i = k) (m : ℤ) (hm : 0 + n = m) (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q k))),
      IsTwPair μ → μ.cup E hm (one q E) a = a.cast (by omega) hk := by
    intro k hk m hm μ hμ
    subst hk
    obtain rfl : m = n := by omega
    exact one_mul_of_pair q E hE _ i hm μ hμ a
  exact key (0 + i) (by ring) (0 + n) rfl (twPair q 0 i) ((GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q 0 i).1)

end GlobalTheory.EtC.CupGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorSquarePerfectProjection
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

theorem tensorSquare_perfectProjection (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (A : Type) [CommRing A] [Algebra k A] (π : A →ₐ[k] A) :
    ((∀ a : A, IsNilpotent (a - π a)) ∧ ∀ a : A, ∃ b : A, π a = π b ^ p) → ((∀ a : A ⊗[k] A, IsNilpotent (a - Algebra.TensorProduct.map π π a)) ∧ ∀ a : A ⊗[k] A, ∃ b : A ⊗[k] A, Algebra.TensorProduct.map π π a = Algebra.TensorProduct.map π π b ^ p) := by
  rintro ⟨h1, h2⟩
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hpA : ((p : ℕ) : A ⊗[k] A) = 0 := by
    rw [← map_natCast (algebraMap k (A ⊗[k] A)) p, CharP.cast_eq_zero, map_zero]
  refine ⟨fun a => ?_, fun a => ?_⟩
  · rw [← mem_nilradical]
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [Algebra.TensorProduct.map_tmul]
      have e : a ⊗ₜ[k] b - π a ⊗ₜ[k] π b = (a - π a) ⊗ₜ[k] b + π a ⊗ₜ[k] (b - π b) := by
        rw [TensorProduct.sub_tmul, TensorProduct.tmul_sub]; abel
      rw [e]
      refine Ideal.add_mem _ ?_ ?_
      · have : (a - π a) ⊗ₜ[k] b = Algebra.TensorProduct.includeLeft (S := k) (B := A) (a - π a) * ((1 : A) ⊗ₜ[k] b) := by
          simp [Algebra.TensorProduct.tmul_mul_tmul]
        rw [this]
        exact Ideal.mul_mem_right _ _ (mem_nilradical.2 ((h1 a).map _))
      · have : π a ⊗ₜ[k] (b - π b) = ((π a) ⊗ₜ[k] (1 : A)) * Algebra.TensorProduct.includeRight (R := k) (A := A) (b - π b) := by
          simp [Algebra.TensorProduct.tmul_mul_tmul]
        rw [this]
        exact Ideal.mul_mem_left _ _ (mem_nilradical.2 ((h1 b).map _))
    | add x y hx hy =>
      rw [map_add (f := _), add_sub_add_comm]
      exact Ideal.add_mem _ hx hy
  · induction a using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp [hp0]⟩
    | tmul a b =>
      obtain ⟨a', ha⟩ := h2 a
      obtain ⟨b', hb⟩ := h2 b
      refine ⟨a' ⊗ₜ[k] b', ?_⟩
      simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_pow, ha, hb]
    | add x y hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨v, hv⟩ := hy
      refine ⟨u + v, ?_⟩
      rw [map_add (f := _), map_add (f := _), hu, hv, ← frobRing_apply hpA, ← frobRing_apply hpA, ← frobRing_apply hpA, map_add (f := _)]

end GlobalTheory
end

