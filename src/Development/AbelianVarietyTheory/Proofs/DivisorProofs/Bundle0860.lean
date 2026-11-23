module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0816
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0842
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRepresentationSpectralProjectors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0823
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0840
public import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelTypeHeckeKilledCorrespondMatchingIso
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.CuspMult.EqTrans

theorem asAlg_comp {H H' X : Type} [Group H] [Group H'] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H' X)
    (e : H ≃* H') (x : MonoidAlgebra ℂ H) :
    Representation.asAlgebraHom (ρ.comp e.toMonoidHom : Representation ℂ H X) x =
      ρ.asAlgebraHom (MonoidAlgebra.domCongr ℂ ℂ e x) := by
  have : Representation.asAlgebraHom (ρ.comp e.toMonoidHom : Representation ℂ H X) =
      ρ.asAlgebraHom.comp (MonoidAlgebra.domCongr ℂ ℂ e).toAlgHom := by
    apply MonoidAlgebra.algHom_ext
    · intro g
      simp
    · exact Subsingleton.elim _ _
  rw [this]; rfl

theorem killed_comp {H H' X : Type} [Group H] [Group H'] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H' X)
    (e : H ≃* H') (I : Set (MonoidAlgebra ℂ H)) (I' : Set (MonoidAlgebra ℂ H'))
    (h1 : ∀ x ∈ I, MonoidAlgebra.domCongr ℂ ℂ e x ∈ I')
    (h2 : ∀ x ∈ I', MonoidAlgebra.domCongr ℂ ℂ e.symm x ∈ I) :
    killed (ρ.comp e.toMonoidHom : Representation ℂ H X) I = killed ρ I' := by
  ext v
  rw [mem_killed, mem_killed]
  constructor
  · intro h x hx
    have := h _ (h2 x hx)
    rw [asAlg_comp, ← MonoidAlgebra.domCongr_symm, AlgEquiv.apply_symm_apply] at this
    exact this
  · intro h x hx
    rw [asAlg_comp]
    exact h _ (h1 x hx)

theorem isDC_map {H H' : Type} [Group H] [Group H'] (e : H ≃* H') (J : Subgroup H) (J' : Subgroup H')
    (hJ : ∀ g, g ∈ J ↔ e g ∈ J') (x : H) (R : Finset H) (h : Bridge.IsDC J x R) :
    Bridge.IsDC J' (e x) (R.map e.toEquiv.toEmbedding) := by
  have hJ' : ∀ g' : J', e.symm g' ∈ J := fun g' => (hJ _).2 (by simp)
  refine ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.1 ha
    obtain ⟨k₁, k₂, rfl⟩ := h.1 b hb
    exact ⟨⟨e k₁, (hJ _).1 k₁.2⟩, ⟨e k₂, (hJ _).1 k₂.2⟩, by simp⟩
  · rintro g ⟨k₁, k₂, rfl⟩
    obtain ⟨a, ⟨ha, ha'⟩, hu⟩ := h.2 (e.symm k₁ * x * e.symm k₂) ⟨⟨_, hJ' k₁⟩, ⟨_, hJ' k₂⟩, rfl⟩
    refine ⟨e a, ⟨Finset.mem_map.2 ⟨a, ha, rfl⟩, ?_⟩, ?_⟩
    · have := (hJ _).1 ha'
      simpa using this
    · rintro b ⟨hb, hb'⟩
      obtain ⟨b, hbR, rfl⟩ := Finset.mem_map.1 hb
      have : b = a := hu b ⟨hbR, (hJ _).2 (by simpa using hb')⟩
      rw [this]; rfl

variable {D : D7}

theorem mem_levG (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (r t : ℕ) (hr : r ≤ V.rank) (Pg : Finset (Pl D.host.E))
    (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (P : LevelP Pg r ℂ) (k : GfC V) :
    (k : GA D V) ∈ levG V β (withP (princDat V.rank r t hr Pg χ) P) ↔
      finE V (k : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) ∧
        (rTup β (princDat V.rank r t hr Pg χ) (finE V (k : GA D V)) : G0 Pg r) ∈ P.H :=
  ⟨fun h => h.2, fun h => ⟨k.2, h⟩⟩

theorem levChi_eq (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (r t : ℕ) (hr : r ≤ V.rank) (Pg : Finset (Pl D.host.E))
    (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (P : LevelP Pg r ℂ) (k : GA D V) :
    levChi V β (withP (princDat V.rank r t hr Pg χ) P) k =
      ((ext1 P.H P.chi (rTup β (princDat V.rank r t hr Pg χ) (finE V k) : G0 Pg r) : ℂˣ) : ℂ) := by
  unfold levChi levFn
  congr 1
  have h1 : (withP (princDat V.rank r t hr Pg χ) P).s = 0 := rfl
  have h2 : (withP (princDat V.rank r t hr Pg χ) P).Q = ∅ := rfl
  rw [h1, h2]
  simp only [Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one]
  rfl

theorem map_mem (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (r t : ℕ) (hr : r ≤ V.rank)
    (hr' : r ≤ V'.rank) (Pg : Finset (Pl D.host.E)) (χ χ' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Φ : GfC V ≃* GfC V')
    {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 Pg r) (c : G → ℂ) (P : LevelP Pg r ℂ) {Pl0 : Type} (ok : Set Pl0)
    (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]) (hrk : V.rank = V'.rank)
    (h1 : ∀ κ : GfC V, finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) ↔
      finE V' (Φ κ : GA D V') ∈ parLev D.sp.cm V'.gram β' (princDat V'.rank r t hr' Pg χ'))
    (h2 : ∀ κ : GfC V, finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) →
      (rTup β' (princDat V'.rank r t hr' Pg χ') (finE V' (Φ κ : GA D V')) : G0 Pg r) =
        (rTup β (princDat V.rank r t hr Pg χ) (finE V (κ : GA D V)) : G0 Pg r))
    (h3 : ∀ P0 ∈ ok, ∀ k (α : GfC V), IsHeckeAt V (pl P0) k α ↔ IsHeckeAt V' (pl P0) k (Φ α))
    (x : MonoidAlgebra ℂ (GfC V)) (hx : x ∈ eqSet V β (princDat V.rank r t hr Pg χ) eG c P ok pl q Sg) :
    MonoidAlgebra.domCongr ℂ ℂ Φ x ∈ eqSet V' β' (princDat V'.rank r t hr' Pg χ') eG c P ok pl q Sg := by
  have hlev : ∀ (P : LevelP Pg r ℂ) (k : GfC V), (k : GA D V) ∈ levG V β (withP (princDat V.rank r t hr Pg χ) P) ↔
      (Φ k : GA D V') ∈ levG V' β' (withP (princDat V'.rank r t hr' Pg χ') P) := by
    intro P k
    rw [mem_levG, mem_levG]
    constructor
    · rintro ⟨a, b⟩
      exact ⟨(h1 k).1 a, by rw [h2 k a]; exact b⟩
    · rintro ⟨a, b⟩
      have a' := (h1 k).2 a
      exact ⟨a', by rw [← h2 k a']; exact b⟩
  rcases hx with (⟨k, hk, rfl⟩ | ⟨κ, hκ, rfl⟩) | ⟨P0, hP0, k, hk, α, R, hα, hR, rfl⟩
  · refine Or.inl (Or.inl ⟨Φ k, (hlev P k).1 hk, ?_⟩)
    rw [levChi_eq, levChi_eq, h2 k ((mem_levG V β r t hr Pg χ P k).1 hk).1, map_sub, MonoidAlgebra.domCongr_single,
      MonoidAlgebra.domCongr_single, map_one Φ]
  · refine Or.inl (Or.inr ⟨fun g => Φ (κ g), fun g => ⟨(Φ (κ g)).2, (h1 _).1 (hκ g).2.1, ?_⟩, ?_⟩)
    · exact (h2 _ (hκ g).2.1).trans (hκ g).2.2
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, MonoidAlgebra.domCongr_single, map_one Φ]
        simp only [MonoidAlgebra.domCongr_single]
  · refine Or.inr ⟨P0, hP0, k, hrk ▸ hk, Φ α, R.map Φ.toEquiv.toEmbedding, (h3 P0 hP0 k α).1 hα, ?_, ?_⟩
    · rw [← map_inv Φ]
      exact isDC_map Φ _ _ (fun g => hlev (LevelP.triv Pg r ℂ) g) _ _ hR
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, MonoidAlgebra.domCongr_single, map_one Φ, Finset.sum_map]
        simp only [MonoidAlgebra.domCongr_single]
        rfl

theorem killed_eqSet_comp : ∀ {D : D7} (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (r t : ℕ) (hr : r ≤ V.rank) (hr' : r ≤ V'.rank) (Pg : Finset (Pl D.host.E)) (χ χ' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Φ : GfC V ≃ₜ* GfC V') {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 Pg r) (c : G → ℂ) (P : LevelP Pg r ℂ) {Pl0 : Type} (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]) (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GfC V') X), V.rank = V'.rank → (∀ κ : GfC V, finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) ↔ finE V' (Φ κ : GA D V') ∈ parLev D.sp.cm V'.gram β' (princDat V'.rank r t hr' Pg χ')) → (∀ κ : GfC V, finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) → (rTup β' (princDat V'.rank r t hr' Pg χ') (finE V' (Φ κ : GA D V')) : G0 Pg r) = (rTup β (princDat V.rank r t hr Pg χ) (finE V (κ : GA D V)) : G0 Pg r)) → (∀ P0 ∈ ok, ∀ k (α : GfC V), IsHeckeAt V (pl P0) k α ↔ IsHeckeAt V' (pl P0) k (Φ α)) → killed (ρ.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ (GfC V) X) (eqSet V β (princDat V.rank r t hr Pg χ) eG c P ok pl q Sg) = killed ρ (eqSet V' β' (princDat V'.rank r t hr' Pg χ') eG c P ok pl q Sg) := by
  intro D V V' β β' r t hr hr' Pg χ χ' Φ G _ _ eG c P Pl0 ok pl q Sg X _ _ ρ hrk h1 h2 h3
  refine killed_comp ρ Φ.toMulEquiv _ _
    (map_mem V V' β β' r t hr hr' Pg χ χ' Φ.toMulEquiv eG c P ok pl q Sg hrk h1 h2 h3) ?_
  have e : ∀ κ : GfC V', Φ (Φ.toMulEquiv.symm κ) = κ := fun κ => Φ.toMulEquiv.apply_symm_apply κ
  refine map_mem V' V β' β r t hr' hr Pg χ' χ Φ.toMulEquiv.symm eG c P ok pl q Sg hrk.symm ?_ ?_ ?_
  · intro κ
    rw [h1, e]
  · intro κ hκ
    have := h2 (Φ.toMulEquiv.symm κ) ((h1 _).2 (by rw [e]; exact hκ))
    rw [e] at this
    exact this.symm
  · intro P0 hP0 k α
    rw [h3 P0 hP0, e]

end GlobalTheory.CuspMult.EqTrans
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionOfComplexExpIntertwinesAction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

theorem GlobalTheory.UPel.HT.lie_of_complexExp : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) (e : (Fin D.g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)), IsAbelianScheme A → SmoothOfRelativeDimension D.g A.hom → IsExp (𝟙 (Sp ℂ)) e → (∀ a z, e (ρ a *ᵥ z) = e z ≫ act.act a) → b.IsType σ ρ → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Sp ℂ), x ≫ spMap σ = spMap β → ∀ v : epsPtR x ⟶ A, IsTanScal act x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ A), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧ v = (List.ofFn w).prod) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp ℂ) (β : R →+* k), x ≫ spMap σ = spMap β → ∀ i, LieMult (act.toF D) x (β.comp (b.t i)) D.m := by
  intro p _ D R _ b N σ ρ A _ _ act e hab hsm hexp hlin hty
  have hsmooth : Smooth A.hom := SmoothOfRelativeDimension.smooth D.g A.hom
  obtain ⟨n, M, hT⟩ := GlobalTheory.T.exists_tangent_coords_base_change_smooth_comm_group ℂ A hsmooth
  obtain ⟨T0, h0inj, h0tan, h0add, h0sc, h0act⟩ := hT ℂ (RingHom.id ℂ)
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := by simp [spMap]
  obtain ⟨L, hL⟩ := GlobalTheory.ExpCoord.expCoord D.g n A e (spMap (RingHom.id ℂ)) T0 hid hexp h0inj h0tan h0add h0sc
  have hLρ : ∀ (a : D.O) w, L (ρ a *ᵥ w) = M (act.act a) *ᵥ L w := fun a w => by
    have := hL (act.act a) (act.hom a) ((M (act.act a)).map (RingHom.id ℂ)) (ρ a)
      (fun c => h0act _ (act.hom a) c) (hlin a) w
    simpa using this
  have hn : n = D.g := by simpa using L.finrank_eq.symm
  subst hn
  set P : Matrix (Fin D.g) (Fin D.g) ℂ := LinearMap.toMatrix' L.toLinearMap with hP
  have hPv : ∀ w, P *ᵥ w = L w := fun w => LinearMap.toMatrix'_mulVec _ w
  have hMP : ∀ a, M (act.act a) * P = P * ρ a := fun a => by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun w => ?_
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hPv]
    exact (hLρ a w).symm
  have hPdet : IsUnit P.det := by
    rw [hP, LinearMap.det_toMatrix']
    exact LinearEquiv.isUnit_det' L
  have key : ∀ (R' : Type) [CommRing R'] (j : ℂ →+* R'), ∃ T' : (Fin D.g → R') → (epsPtR (spMap j) ⟶ A),
      Function.Injective T' ∧
      (∀ v : epsPtR (spMap j) ⟶ A, spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left =
        (1 : Over.mk (spMap j) ⟶ A).left ↔ v ∈ Set.range T') ∧
      (∀ c c', T' (c + c') = T' c * T' c') ∧
      (∀ (s : R') c, (T' (s • c)).left = spMap (epsScaleR s) ≫ (T' c).left) ∧
      ∀ (a : D.O) c, T' c ≫ act.act a = T' ((ρ a).map j *ᵥ c) := by
    intro R' _ j
    obtain ⟨T, hinj, htan, hadd, hsc, hact⟩ := hT R' j
    have hu : IsUnit (P.map j) := by
      rw [Matrix.isUnit_iff_isUnit_det]
      have : (P.map j).det = j P.det := by rw [RingHom.map_det]; rfl
      rw [this]
      exact hPdet.map j
    have hinv : (P.map j)⁻¹ * P.map j = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)
    have hPinj : Function.Injective (P.map j).mulVec := fun c c' h => by
      have := congrArg ((P.map j)⁻¹ *ᵥ ·) h
      simpa [Matrix.mulVec_mulVec, hinv] using this
    have hPsurj : Function.Surjective (P.map j).mulVec := Matrix.mulVec_surjective_iff_isUnit.2 hu
    refine ⟨fun c => T (P.map j *ᵥ c), hinj.comp hPinj, fun v => ?_, fun c c' => ?_, fun s c => ?_, fun a c => ?_⟩
    · rw [htan v]
      constructor
      · rintro ⟨y, rfl⟩
        obtain ⟨c, rfl⟩ := hPsurj y
        exact ⟨c, rfl⟩
      · rintro ⟨c, rfl⟩
        exact ⟨_, rfl⟩
    · simp only [Matrix.mulVec_add, hadd]
    · simp only [Matrix.mulVec_smul, hsc]
    · simp only
      rw [hact _ (act.hom a), Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Matrix.map_mul, hMP]
  obtain ⟨E, hE1, hE2, hE3, hE4, hE5⟩ := _root_.GlobalTheory.UPel.HT.LieProj.lie_projectors p D R b σ ρ hty
  have hroot : σ b.ρ ^ 2 - D.tr * σ b.ρ + D.nm = 0 := by
    have := congrArg σ b.ρ_root
    simpa using this
  have hne : σ b.ρ ≠ (D.tr : ℂ) - σ b.ρ := by
    intro h
    have h2 : (((D.tr ^ 2 - 4 * D.nm : ℤ)) : ℂ) = 0 := by
      push_cast
      linear_combination (2 * σ b.ρ - D.tr) * h - 4 * hroot
    have := D.disc_neg
    rw [Int.cast_eq_zero] at h2
    omega
  have hdist : ∀ i j, i ≠ j → ∃ c, (σ.comp (b.t i)) c ≠ (σ.comp (b.t j)) c := by
    intro i j hij
    by_contra hc
    push Not at hc
    have hle : Ideal.span (Set.range fun x => b.t i x - b.t j x) ≤ RingHom.ker σ := by
      rw [Ideal.span_le]
      rintro _ ⟨x, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub]
      exact sub_eq_zero.2 (hc x)
    rw [b.comax i j hij, top_le_iff] at hle
    have h1 : (1 : R) ∈ RingHom.ker σ := hle ▸ Submodule.mem_top
    simp at h1
  have hE5' : (σ b.ρ - ((D.tr : ℂ) - σ b.ρ)) • ∑ i, E i =
      (ρ.comp (algebraMap (𝓞 D.F) D.O)) D.ω - ((D.tr : ℂ) - σ b.ρ) • (1 : Matrix (Fin D.g) (Fin D.g) ℂ) := by
    rw [show σ b.ρ - ((D.tr : ℂ) - σ b.ρ) = 2 * σ b.ρ - D.tr by ring]
    exact hE5
  have hbc := GlobalTheory.SpecBC.baseChange_specDecomp D.g D.a D.m (𝓞 D.F) (ρ.comp (algebraMap (𝓞 D.F) D.O)) (fun i => σ.comp (b.t i)) D.ω
    (σ b.ρ) ((D.tr : ℂ) - σ b.ρ) E hne hdist hE1 hE2 hE3 hE4 hE5'
  have hpt : ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Sp ℂ), x ≫ spMap σ = spMap β →
      ∃ j : ℂ →+* R', x = spMap j ∧ β = j.comp σ := by
    intro R' _ β x hx
    have hxj : x = spMap (Spec.preimage x).hom := by simp [spMap]
    generalize (Spec.preimage x).hom = j at hxj
    subst hxj
    refine ⟨j, rfl, ?_⟩
    have e1 : spMap (j.comp σ) = spMap j ≫ spMap σ := by
      simp [spMap, ← Spec.map_comp]
    rw [hx] at e1
    have := Spec.map_injective e1
    exact (congrArg CommRingCat.Hom.hom this).symm
  refine ⟨fun R' _ β x hx v hv => ?_, fun k _ _ x β hx i => ?_⟩
  · obtain ⟨j, rfl, rfl⟩ := hpt R' β x hx
    obtain ⟨T', h1, h2, h3, h4, h5⟩ := key R' j
    exact GlobalTheory.LieCoordMult.tanScal_decomp D.O (𝓞 D.F) (Sp ℂ) A act R' (spMap j) D.g D.a T' (fun a => (ρ a).map j)
      (algebraMap (𝓞 D.F) D.O) D.ω ((j.comp σ) b.ρ) (fun i c => (j.comp σ) (b.t i c)) h1 h2 h3 h4 h5
      (fun y hy => hbc.1 R' j y hy) v hv
  · obtain ⟨j, rfl, rfl⟩ := hpt k β x hx
    obtain ⟨T', h1, h2, h3, h4, h5⟩ := key k j
    exact (GlobalTheory.LieCoordMult.lieMult_iff_finrank_eig ℂ A (𝓞 D.F) (act.toF D) D.g k j T' (fun c => (ρ (algebraMap (𝓞 D.F) D.O c)).map j) h1 h2 h3 h4
      (fun a c => h5 _ c) ((j.comp σ).comp (b.t i)) D.m).2 (hbc.2 k j i (by simp only [RingHom.comp_apply, b.t_ω]))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapMulRightEqOfFundamentalDomain
section
open MeasureTheory
open scoped ENNReal NNReal

namespace GlobalTheory.ConjModulus

theorem map_mul_right_eq_of_fundamentalDomain {H : Type} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H]
    [MeasurableSpace H] [BorelSpace H] (Λ : Subgroup H) [Countable Λ] (ρ : Measure H)
    [ρ.IsHaarMeasure] (𝓡 : Set H) (h𝓡 : IsFundamentalDomain Λ 𝓡 ρ) (hfin : ρ 𝓡 ≠ ⊤) (x₀ : H) :
    ρ.map (· * x₀) = ρ := by
  haveI : (ρ.map (· * x₀)).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right ρ x₀
  have hc := Measure.isMulLeftInvariant_eq_smul (ρ.map (· * x₀)) ρ
  set c := Measure.haarScalarFactor (ρ.map (· * x₀)) ρ
  have h' : IsFundamentalDomain Λ ((· * x₀) ⁻¹' 𝓡) ρ := by
    refine h𝓡.preimage_of_equiv (quasiMeasurePreserving_mul_right ρ x₀) (e := id)
      Function.bijective_id ?_
    intro g x
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hm : ρ ((· * x₀) ⁻¹' 𝓡) = ρ 𝓡 := h'.measure_eq h𝓡
  have h0 : ρ 𝓡 ≠ 0 := h𝓡.measure_ne_zero (NeZero.ne ρ)
  have hmap : (ρ.map (· * x₀)) 𝓡 = ρ ((· * x₀) ⁻¹' 𝓡) :=
    MeasurableEquiv.map_apply (MeasurableEquiv.mulRight x₀) 𝓡
  have h1 : (c : ℝ≥0∞) * ρ 𝓡 = 1 * ρ 𝓡 := by
    calc (c : ℝ≥0∞) * ρ 𝓡 = (c • ρ) 𝓡 := by simp [Measure.smul_apply]
      _ = (ρ.map (· * x₀)) 𝓡 := by rw [hc]
      _ = 1 * ρ 𝓡 := by rw [one_mul]; exact hmap.trans hm
  have hc1 : c = 1 := by
    have := (ENNReal.mul_left_inj h0 hfin).1 h1
    exact_mod_cast this
  rw [hc, hc1, one_smul]

def conjB {H G : Type} [Group H] [Group G] (ι : H →* G) (B : Subgroup G)
    (hB : ∀ x : H, ∀ b ∈ B, ι x * b * (ι x)⁻¹ ∈ B) (x : H) (b : B) : B :=
  ⟨ι x * b * (ι x)⁻¹, hB x b b.2⟩

def conjCME {H G : Type} [Group H] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (ι : H →* G) (B : Subgroup G) (hB : ∀ x : H, ∀ b ∈ B, ι x * b * (ι x)⁻¹ ∈ B) (x : H) :
    B ≃ₜ* B where
  toFun := conjB ι B hB x
  invFun := conjB ι B hB x⁻¹
  left_inv b := by apply Subtype.ext; simp [conjB, mul_assoc]
  right_inv b := by apply Subtype.ext; simp [conjB, mul_assoc]
  map_mul' a b := by apply Subtype.ext; simp [conjB, mul_assoc]
  continuous_toFun := continuous_induced_rng.2
    ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  continuous_invFun := continuous_induced_rng.2
    ((continuous_const.mul continuous_subtype_val).mul continuous_const)

theorem conjB_mul {H G : Type} [Group H] [Group G] (ι : H →* G) (B : Subgroup G)
    (hB : ∀ x : H, ∀ b ∈ B, ι x * b * (ι x)⁻¹ ∈ B) (x y : H) :
    conjB ι B hB (x * y) = conjB ι B hB x ∘ conjB ι B hB y := by
  funext b; apply Subtype.ext; simp [conjB, mul_assoc]

end GlobalTheory.ConjModulus

namespace GlobalTheory.ConjModulus

theorem map_conj_eq_self_of_lattice : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (ι : H →* G), Continuous ι → ∀ B : Subgroup G, IsClosed (B : Set G) →
    ∀ (hB : ∀ x : H, ∀ b ∈ B, ι x * b * (ι x)⁻¹ ∈ B) (β : Measure B), β.IsHaarMeasure →
    ∀ (Λ : Subgroup H) [Countable Λ] (ρ : Measure H) (𝓡 : Set H), ρ.IsHaarMeasure → IsFundamentalDomain Λ 𝓡 ρ → ρ 𝓡 ≠ ⊤ →
    (∀ x ∈ Λ, β.map (fun b : B => (⟨ι x * b * (ι x)⁻¹, hB x b b.2⟩ : B)) = β) →
    ∀ x : H, β.map (fun b : B => (⟨ι x * b * (ι x)⁻¹, hB x b b.2⟩ : B)) = β := by
  intro H _ _ _ _ _ _ _ _ G _ _ _ _ _ _ _ _ ι hι B hBc hB β hβ Λ _ ρ 𝓡 hρ h𝓡 hfin hΛ
  haveI := hβ
  haveI := hρ
  haveI : LocallyCompactSpace B := hBc.locallyCompactSpace
  haveI : SecondCountableTopology B := TopologicalSpace.Subtype.secondCountableTopology (B : Set G)
  haveI : SigmaCompactSpace B := inferInstance
  haveI : SigmaFinite β := inferInstance
  have hΛ' : ∀ x ∈ Λ, β.map (conjB ι B hB x) = β := hΛ
  show ∀ x : H, β.map (conjB ι B hB x) = β
  have hφm : ∀ x, Measurable (conjB ι B hB x) := fun x => (conjCME ι B hB x).continuous.measurable
  have hHaar : ∀ x, (β.map (conjB ι B hB x)).IsHaarMeasure := fun x =>
    (conjCME ι B hB x).isHaarMeasure_map β
  obtain ⟨d, hdβ⟩ : ∃ d : H → ℝ≥0, ∀ x, β.map (conjB ι B hB x) = d x • β := ⟨fun x =>
    Measure.haarScalarFactor (β.map (conjB ι B hB x)) β, fun x => by
      haveI := hHaar x; exact Measure.isMulLeftInvariant_eq_smul _ _⟩
  obtain ⟨K, hKc, hK1⟩ := exists_compact_mem_nhds (1 : B)
  have hK0 : β K ≠ 0 := (Measure.measure_pos_of_mem_nhds β hK1).ne'
  have hKt : β K ≠ ⊤ := hKc.measure_lt_top.ne
  have hcancel : ∀ a b : ℝ≥0, a • β = b • β → a = b := by
    intro a b h
    have h2 : (a : ℝ≥0∞) * β K = (b : ℝ≥0∞) * β K := by
      have := congrArg (fun m : Measure B => m K) h
      simpa [Measure.smul_apply] using this
    exact_mod_cast (ENNReal.mul_left_inj hK0 hKt).1 h2
  have hmul : ∀ x y, d (x * y) = d x * d y := by
    intro x y
    apply hcancel
    rw [← hdβ, conjB_mul, ← Measure.map_map (hφm x) (hφm y), hdβ y, Measure.map_smul, hdβ x,
      smul_smul, mul_comm]
    exact (hφm x).aemeasurable
  have hdΛ : ∀ x ∈ Λ, d x = 1 := by
    intro x hx
    apply hcancel
    rw [← hdβ, hΛ' x hx, one_smul]
  have hpos : ∀ x, 0 < d x := by
    intro x
    rw [pos_iff_ne_zero]
    intro h0
    have h1 := congrArg (fun m : Measure B => m Set.univ) (hdβ x)
    simp only [h0, zero_smul, Measure.coe_zero, Pi.zero_apply] at h1
    rw [Measure.map_apply (hφm x) MeasurableSet.univ, Set.preimage_univ] at h1
    exact (Measure.measure_univ_pos.2 (NeZero.ne β)).ne' h1

  have hΦ : Continuous (fun p : H × B => conjB ι B hB p.1 p.2) :=
    continuous_induced_rng.2 (((hι.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).mul (hι.comp continuous_fst).inv)
  have hS : MeasurableSet ((fun p : H × B => conjB ι B hB p.1 p.2) ⁻¹' K) :=
    (hKc.isClosed.preimage hΦ).measurableSet
  have hDm : Measurable fun x => β (conjB ι B hB x ⁻¹' K) := measurable_measure_prodMk_left hS
  have hdK : ∀ x, (d x : ℝ≥0∞) = β (conjB ι B hB x ⁻¹' K) / β K := by
    intro x
    rw [ENNReal.eq_div_iff hK0 hKt, ← Measure.map_apply (hφm x) hKc.isClosed.measurableSet, hdβ x]
    simp [Measure.smul_apply, mul_comm]
  have hdm : Measurable d := by
    apply measurable_coe_nnreal_ennreal_iff.1
    simp_rw [hdK]
    exact hDm.div_const _

  obtain ⟨g, hgm, hgs, hg1⟩ : ∃ g : ℝ≥0 → ℝ≥0∞, Measurable g ∧
      (∀ a b : ℝ≥0, 0 < a → a < b → g a < g b) ∧ ∀ t, g t ≤ 1 := by
    refine ⟨fun t => ENNReal.ofReal ((t : ℝ) / (1 + t)), ?_, ?_, ?_⟩
    · exact (measurable_coe_nnreal_real.div (measurable_const.add measurable_coe_nnreal_real)).ennreal_ofReal
    · intro a b ha hab
      have ha' : (0 : ℝ) < a := ha
      have hab' : (a : ℝ) < b := hab
      have hb' : (0 : ℝ) < b := ha'.trans hab'
      have hpos' : (0 : ℝ) < (b : ℝ) / (1 + b) := div_pos hb' (by linarith)
      simp only
      rw [ENNReal.ofReal_lt_ofReal_iff hpos', div_lt_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    · intro t
      apply ENNReal.ofReal_le_one.2
      rw [div_le_one (by positivity)]
      linarith

  have hR : ∀ x₀ : H, ρ.map (· * x₀) = ρ := map_mul_right_eq_of_fundamentalDomain Λ ρ 𝓡 h𝓡 hfin
  have hfΛ : ∀ (l : Λ) (z : H), g (d (l • z)) = g (d z) := by
    intro l z
    rw [Subgroup.smul_def, smul_eq_mul, hmul, hdΛ _ l.2, one_mul]
  have hshift : ∀ x₀ : H, ∫⁻ z in 𝓡, g (d z) ∂ρ = ∫⁻ z in 𝓡, g (d z * d x₀) ∂ρ := by
    intro x₀
    have hmp : MeasurePreserving (· * x₀) ρ ρ := ⟨measurable_mul_const x₀, hR x₀⟩
    have hemb : MeasurableEmbedding (· * x₀ : H → H) := (MeasurableEquiv.mulRight x₀).measurableEmbedding
    have h' : IsFundamentalDomain Λ ((· * x₀) '' 𝓡) ρ := by
      rw [Set.image_mul_right]
      refine h𝓡.preimage_of_equiv (quasiMeasurePreserving_mul_right ρ x₀⁻¹) (e := id)
        Function.bijective_id ?_
      intro l y
      simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
    have := (h𝓡.setLIntegral_eq h' (fun z => g (d z)) hfΛ).trans
      (hmp.setLIntegral_comp_emb hemb (fun z => g (d z)) 𝓡).symm
    simpa [hmul] using this
  have hne : ρ.restrict 𝓡 ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]; exact h𝓡.measure_ne_zero (NeZero.ne ρ)
  have hfinI : ∀ c : ℝ≥0, ∫⁻ z in 𝓡, g (d z * c) ∂ρ ≠ ⊤ := by
    intro c
    refine ne_top_of_le_ne_top (b := ∫⁻ _ in 𝓡, 1 ∂ρ) ?_ (lintegral_mono fun z => hg1 _)
    rw [setLIntegral_const, one_mul]; exact hfin
  have hd1 : ∀ x, d x = 1 := by
    intro x₀
    by_contra hne1
    have hsh := hshift x₀
    rcases lt_or_gt_of_ne hne1 with hlt | hgt
    · have hlt' : ∫⁻ z in 𝓡, g (d z * d x₀) ∂ρ < ∫⁻ z in 𝓡, g (d z) ∂ρ := by
        refine lintegral_strict_mono hne (hgm.comp hdm).aemeasurable (hfinI _)
          (Filter.Eventually.of_forall fun z => ?_)
        exact hgs _ _ (mul_pos (hpos z) (hpos x₀)) (mul_lt_of_lt_one_right (hpos z) hlt)
      exact hlt'.ne hsh.symm
    · have hlt' : ∫⁻ z in 𝓡, g (d z) ∂ρ < ∫⁻ z in 𝓡, g (d z * d x₀) ∂ρ := by
        have h1 := hfinI 1
        simp only [mul_one] at h1
        refine lintegral_strict_mono hne ((hgm.comp (hdm.mul_const _))).aemeasurable h1
          (Filter.Eventually.of_forall fun z => ?_)
        exact hgs _ _ (hpos z) (lt_mul_of_one_lt_right (hpos z) hgt)
      exact hlt'.ne hsh
  intro x
  rw [hdβ x, hd1 x, one_smul]

end GlobalTheory.ConjModulus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbKEqZeroOfCharpolyNotSeparable
section
namespace GlobalTheory

theorem orbK_eq_zero_of_charpoly_not_separable (G : Type) [Group G] (k : Type) [Field k] (n : ℕ)
    (π : G →* GL (Fin n) k) (K : Subgroup G) (δ : G) (f : G → ℂ)
    (hf : ∀ g, f g ≠ 0 → ((π g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly.Separable)
    (hδ : ¬ ((π δ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly.Separable) :
    GlobalTheory.LKCount.orbK (MonoidHom.id G) K δ f = 0 := by
  unfold GlobalTheory.LKCount.orbK GlobalTheory.LKCount.orbC
  apply finsum_eq_zero_of_forall_eq_zero
  intro q
  have hz : ∀ x : G, f (x⁻¹ * δ * x) = 0 := by
    intro x
    by_contra h
    apply hδ
    have hs := hf _ h
    have hc : ((π (x⁻¹ * δ * x) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly
        = ((π δ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly := by
      rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul,
        Matrix.charpoly_mul_comm, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    rwa [hc] at hs
  simp [hz]

end GlobalTheory
end

