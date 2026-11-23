module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0813
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0821
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0840
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0789
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodFormsEqKilledByGroupAlgebra
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.CuspMult.EqCut

section Cosets

variable {Γ : Type} [Group Γ] {H J : Subgroup Γ}

theorem isDC_sub_iff (hJ : J ≤ H) (a : H) (R : Finset H) :
    Bridge.IsDC (J.subgroupOf H) a R ↔ Bridge.IsDC J (a : Γ) (R.map (Function.Embedding.subtype _)) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun b hb => ?_, ?_⟩
    · obtain ⟨b', hb', rfl⟩ := Finset.mem_map.1 hb
      obtain ⟨k₁, k₂, e⟩ := h1 b' hb'
      exact ⟨⟨k₁.1.1, k₁.2⟩, ⟨k₂.1.1, k₂.2⟩, congrArg Subtype.val e⟩
    · rintro g ⟨k₁, k₂, rfl⟩
      obtain ⟨b, ⟨hb, hb2⟩, hu⟩ := h2 _ ⟨⟨⟨k₁.1, hJ k₁.2⟩, k₁.2⟩, ⟨⟨k₂.1, hJ k₂.2⟩, k₂.2⟩, rfl⟩
      refine ⟨b.1, ⟨Finset.mem_map.2 ⟨b, hb, rfl⟩, hb2⟩, ?_⟩
      rintro y ⟨hy, hy2⟩
      obtain ⟨y', hy', rfl⟩ := Finset.mem_map.1 hy
      exact congrArg Subtype.val (hu y' ⟨hy', hy2⟩)
  · rintro ⟨h1, h2⟩
    refine ⟨fun b hb => ?_, ?_⟩
    · obtain ⟨k₁, k₂, e⟩ := h1 b.1 (Finset.mem_map.2 ⟨b, hb, rfl⟩)
      exact ⟨⟨⟨k₁.1, hJ k₁.2⟩, k₁.2⟩, ⟨⟨k₂.1, hJ k₂.2⟩, k₂.2⟩, Subtype.ext e⟩
    · rintro g ⟨k₁, k₂, rfl⟩
      obtain ⟨b, ⟨hb, hb2⟩, hu⟩ := h2 _ ⟨⟨k₁.1.1, k₁.2⟩, ⟨k₂.1.1, k₂.2⟩, rfl⟩
      obtain ⟨b', hb', rfl⟩ := Finset.mem_map.1 hb
      refine ⟨b', ⟨hb', hb2⟩, ?_⟩
      rintro y ⟨hy, hy2⟩
      exact Subtype.ext (hu y.1 ⟨Finset.mem_map.2 ⟨y, hy, rfl⟩, hy2⟩)

theorem exists_lift_of_isDC (hJ : J ≤ H) (a : H) (R' : Finset Γ) (h : Bridge.IsDC J (a : Γ) R') :
    ∃ R : Finset H, R.map (Function.Embedding.subtype _) = R' := by
  classical
  refine ⟨R'.subtype (· ∈ H), Finset.subtype_map_of_mem fun b hb => ?_⟩
  obtain ⟨k₁, k₂, rfl⟩ := h.1 b hb
  exact H.mul_mem (H.mul_mem (hJ k₁.2) a.2) (hJ k₂.2)

end Cosets

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem levChi_flag {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} (hs : L.s = 0) (hQ : L.Q = ∅)
    (κ : GA D V) : levChi V β (flagL L) κ = 1 := by
  have h2 : ext1 (flagL L).P.H (flagL L).P.chi (rTup β (flagL L) (finE V κ)) = 1 := subgroupCharExtension_one_apply _ _
  have hs' : (flagL L).s = 0 := hs
  have hQ' : (flagL L).Q = ∅ := hQ
  unfold levChi levFn
  rw [h2, hs', hQ']
  simp

theorem levChi_flag1 {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} (hs : L.s = 0) (hQ : L.Q = ∅)
    (κ : GA D V) : levChi V β (flag1L L) κ = 1 := by
  rw [← levChi_flag (β := β) hs hQ κ]
  unfold levChi
  rw [levFn_flag1]

theorem hasType_flag1 {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} (P : LevelP L.Pg L.r ℂ)
    {F : GA D V → ℂ} (hF : HasType V β (withP L P) F) : HasType V β (flag1L L) F := by
  intro κ hκ h
  have e : rTup β L (finE V κ) = 1 := Subgroup.mem_bot.1 hκ.2.2
  have hm : κ ∈ levG V β (withP L P) := by
    refine ⟨hκ.1, hκ.2.1, ?_⟩
    show rTup β L (finE V κ) ∈ P.H
    rw [e]; exact P.H.one_mem
  rw [hF κ hm h]
  unfold levChi
  rw [levFn_withP, e, blockDiagonalExtendByOnePrimeField_one, one_mul, levFn_flag1]

theorem gaL_apply {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} (hs : L.s = 0) (hQ : L.Q = ∅)
    {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) {F : GA D V → ℂ}
    (hF : HasType V β (flag1L L) F) (κ : G → GA D V) (hκ : ∀ g, IsLevelLift V β L (eG g) (κ g)) (h : GA D V) :
    gaL V β L eG c F h = ∑ g, c g * F (h * κ g) := by
  unfold gaL
  rw [LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  have := level_action_spec hF ⟨κ g, hκ g⟩ (κ g) (hκ g) h
  rw [levChi_flag hs hQ, inv_one, one_mul] at this
  rw [← this]
  rfl

theorem alg_sum (M : DSModel V S) {ι : Type} (s : Finset ι) (κ : ι → GfC V) (c : ι → ℂ) (a : ℂ) (T : MMap M) :
    (finRep M).asAlgebraHom (∑ i ∈ s, MonoidAlgebra.single (κ i) (c i) - MonoidAlgebra.single 1 a) T = 0 ↔
      ∀ v x, ∑ i ∈ s, c i * T v (x * (κ i : GA D V)) = a * T v x := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum, LinearMap.sub_apply, sub_eq_zero, LinearMap.sum_apply]
  simp only [Representation.asAlgebraHom_single, map_one, LinearMap.smul_apply, Module.End.one_apply]
  rw [MultilinearMap.ext_iff]
  refine forall_congr' fun v => ?_
  rw [funext_iff]
  refine forall_congr' fun x => ?_
  rw [MultilinearMap.sum_apply, Finset.sum_apply]
  rfl

theorem alg_one (M : DSModel V S) (k : GfC V) (a : ℂ) (T : MMap M) :
    (finRep M).asAlgebraHom (MonoidAlgebra.single k 1 - MonoidAlgebra.single 1 a) T = 0 ↔
      ∀ v x, T v (x * (k : GA D V)) = a * T v x := by
  have := alg_sum M (Finset.univ : Finset Unit) (fun _ => k) (fun _ => 1) a T
  simpa only [Finset.univ_unique, Finset.sum_singleton, one_mul] using this

theorem mem_hPart (M : DSModel V S) (J : Subgroup (GA D V)) {Pl0 : Type} (ok : Set Pl0)
    (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]) (T : MMap M) :
    T ∈ hPart M J ok pl q Sg ↔ ∀ P ∈ ok, ∀ k ≤ V.rank, ∀ α, IsHeckeAt V (pl P) k α → ∀ R, Bridge.IsDC J α⁻¹ R →
      ∀ v x, ∑ γ ∈ R, T v (x * γ) = ((Sg P).coeff k / ((-1) ^ k * (q P : ℂ) ^ (k * (k - 1) / 2))) * T v x := by
  unfold hPart
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, MultilinearMap.ext_iff, funext_iff]
  rfl

theorem good_hecke_eq_killed : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank) {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (P : LevelP L.Pg L.r ℂ) {Pl0 : Type} (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]), L.s = 0 → L.Q = ∅ → LiftsExist V β L → goodPart θ M (levS V β (withP L P)) (levChi V β (withP L P)) (gaL V β L eG c) ⊓ hPart M (levG V β (flag1L L)) ok pl q Sg = allMaps θ M ⊓ killed (finRep M) (eqSet V β L eG c P ok pl q Sg) := by
  intro D V S θ M β L G _ _ eG c P Pl0 ok pl q Sg hs hQ hlift
  have hJ : levG V β (flag1L L) ≤ GfC V := fun _ h => h.1
  ext T
  rw [Submodule.mem_inf, Submodule.mem_inf, mem_goodPart, mem_killed, mem_hPart, GlobalTheory.MultMem.mem_mult_iff,
    GlobalTheory.MultMem.mem_mult_iff]
  constructor
  · rintro ⟨⟨hm, hg⟩, hh⟩
    refine ⟨⟨hm.aut, hm.cusp, fun _ _ h => h.elim, hm.equiv, hm.cont⟩, ?_⟩
    rintro x ((⟨k, hk, rfl⟩ | ⟨κ, hκ, rfl⟩) | ⟨P0, hP0, k, hk, α, R, hα, hR, rfl⟩)
    · exact (alg_one M k _ T).2 fun v x => hm.lev v k hk x
    · refine (alg_sum M _ κ c 1 T).2 fun v x => ?_
      have hF : HasType V β (flag1L L) (T v) := hasType_flag1 P fun k hk h => hm.lev v k hk h
      rw [← gaL_apply hs hQ eG c hF (fun g => κ g) hκ x, hg v, one_mul]
    · refine (alg_sum M R (fun γ => γ) (fun _ => 1) _ T).2 fun v x => ?_
      have := hh P0 hP0 k hk α hα _ ((isDC_sub_iff hJ α⁻¹ R).1 hR) v x
      rw [Finset.sum_map] at this
      simp only [one_mul]
      exact this
  · rintro ⟨hm, hk⟩
    have hlev : ∀ v, HasType V β (withP L P) (T v) := fun v k hkk x =>
      (alg_one M ⟨k, hkk.1⟩ _ T).1 (hk _ (Or.inl (Or.inl ⟨⟨k, hkk.1⟩, hkk, rfl⟩))) v x
    refine ⟨⟨⟨hm.aut, hm.cusp, fun v k hkk x => hlev v k hkk x, hm.equiv, hm.cont⟩, fun v => ?_⟩, ?_⟩
    · choose κ hκ using fun g => hlift (eG g)
      funext x
      rw [gaL_apply hs hQ eG c (hasType_flag1 P (hlev v)) κ hκ x]
      have := (alg_sum M Finset.univ (fun g => (⟨κ g, (hκ g).1⟩ : GfC V)) c 1 T).1
        (hk _ (Or.inl (Or.inr ⟨fun g => ⟨κ g, (hκ g).1⟩, hκ, rfl⟩))) v x
      rw [one_mul] at this
      exact this
    · intro P0 hP0 k hkr α hα R' hR' v x
      have hαf : α ∈ GfC V := by
        obtain ⟨e, ϖ, -, -, -, h⟩ := hα
        exact h.1
      obtain ⟨R, rfl⟩ := exists_lift_of_isDC hJ (⟨α, hαf⟩ : GfC V)⁻¹ R' hR'
      have hR := (isDC_sub_iff hJ (⟨α, hαf⟩ : GfC V)⁻¹ R).2 hR'
      have := (alg_sum M R (fun γ => γ) (fun _ => 1) _ T).1
        (hk _ (Or.inr ⟨P0, hP0, k, hkr, ⟨α, hαf⟩, R, hα, hR, rfl⟩)) v x
      simp only [one_mul] at this
      rw [Finset.sum_map]
      exact this

end GlobalTheory.CuspMult.EqCut

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIdempotentCoefficientConjugate
section
noncomputable section

open Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters

namespace GlobalTheory.GoodIdemFlip

section Local

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] {r : ℕ}

def invParam (s : SSParam p K r) : SSParam p K r := ⟨s.1, fun c => (s.2 c)⁻¹⟩

theorem cycChar_invParam (s : SSParam p K r) (c : Cyc (invParam s).1) : cycChar (invParam s) c = (cycChar s c)⁻¹ := by
  ext x; rfl

theorem rootChar_invParam (s : SSParam p K r) (x : Σ c : Cyc (invParam s).1, Fin (cycLen (invParam s).1 c)) :
    rootChar (invParam s) x = (rootChar s x)⁻¹ := by
  have h : rootChar (invParam s) x = (cycChar s x.1)⁻¹ ^ (p ^ x.2.val) := by
    rw [← cycChar_invParam s x.1]; rfl
  rw [h, inv_pow]
  rfl

theorem congrMod_inv {A : Type} [CommGroup A] (l : ℕ) (a b : A) : CongrMod l a⁻¹ b⁻¹ ↔ CongrMod l a b := by
  have : a⁻¹ / b⁻¹ = (a / b)⁻¹ := by rw [inv_div_inv, inv_div]
  simp only [CongrMod, this, inv_pow, inv_eq_one]

theorem congrMod_inv_left {A : Type} [CommGroup A] (l : ℕ) (a b : A) : CongrMod l a⁻¹ b ↔ CongrMod l a b⁻¹ := by
  rw [← congrMod_inv, inv_inv]

theorem inv_comp_baseNorm (χ : (ZMod p)ˣ →* Kˣ) (D : ℕ) :
    χ⁻¹.comp (baseNorm p D) = (χ.comp (baseNorm p D))⁻¹ := by
  ext x; rfl

theorem goodAt_flip {ι J : Type} (χ : J → ((ZMod p)ˣ →* Kˣ)) (s s' : ι → SSParam p K r)
    (h : ∀ v, s' v = s v ∨ s' v = invParam (s v)) (hs : GoodAt χ s) : GoodAt χ s' := by
  obtain ⟨h1, h2, ⟨h3, h3'⟩, h4, v5, h5⟩ := hs
  refine ⟨fun v => ?_, fun l hl hl' v => ?_, ⟨fun l hl hl' v => ?_, fun v => ?_⟩, ?_, v5, ?_⟩
  · rcases h v with e | e <;> rw [e]
    · exact h1 v
    · intro x y hxy
      rw [rootChar_invParam, rootChar_invParam] at hxy
      exact h1 v (inv_injective hxy)
  · rcases h v with e | e <;> rw [e]
    · exact h2 l hl hl' v
    · intro x y hxy
      rw [rootChar_invParam, rootChar_invParam, congrMod_inv]
      exact h2 l hl hl' v x y hxy
  · rcases h v with e | e <;> rw [e]
    · exact h3 l hl hl' v
    · intro j c
      have := h3 l hl hl' v j c
      rw [inv_comp_baseNorm] at this
      rw [cycChar_invParam, inv_comp_baseNorm, congrMod_inv, congrMod_inv_left]
      exact this.symm
  · rcases h v with e | e <;> rw [e]
    · exact h3' v
    · intro j x
      have := h3' v j x
      rw [inv_comp_baseNorm] at this
      rw [rootChar_invParam, inv_comp_baseNorm, Ne, Ne, inv_inj, inv_eq_iff_eq_inv]
      exact this.symm
  · rintro ⟨a, ha, ha', hA⟩
    refine h4 ⟨a, ha, ha', fun v => ?_⟩
    have := hA v
    rcases h v with e | e <;> rw [e] at this <;> exact this
  · rcases h v5 with e | e <;> rw [e] <;> exact h5

theorem isConj_inv_inv {G : Type} [Group G] {a b : G} (h : IsConj a b) : IsConj a⁻¹ b⁻¹ := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  exact isConj_iff.2 ⟨c, by group⟩

end Local

section Global

variable {R : Ranks} {H : Host R} {K : Type} [Field K]


open Classical in
def flipAt (S : Set (Sq H)) (x : LevelGroup H) : LevelGroup H := fun v => if v ∈ S then (x v)⁻¹ else x v


open Classical in
def flipParam (S : Set (Sq H)) (s : ∀ v : Sq H, SSParam (H.g v.1) K R.r) : ∀ v : Sq H, SSParam (H.g v.1) K R.r :=
  fun v => if v ∈ S then invParam (s v) else s v

theorem flipAt_flipAt (S : Set (Sq H)) (x : LevelGroup H) : flipAt S (flipAt S x) = x := by
  funext v
  by_cases hv : v ∈ S <;> simp [flipAt, hv]

theorem flipAt_one (S : Set (Sq H)) : flipAt S 1 = 1 := by
  funext v
  by_cases hv : v ∈ S <;> simp [flipAt, hv]

theorem tupleChar_flipParam (S : Set (Sq H)) (s : ∀ v : Sq H, SSParam (H.g v.1) K R.r) :
    tupleChar (flipParam S s) = tupleChar s ∘ flipAt S := by
  funext x
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases hv : v ∈ S
  · simp only [flipParam, flipAt, if_pos hv]
    exact (GlobalTheory.TypeCharacterConjugateInverse.typeChar_conj_inv _ K _ (s v)).2 (x v)
  · simp only [flipParam, flipAt, if_neg hv]

theorem tupleChar_congr (s : ∀ v : Sq H, SSParam (H.g v.1) K R.r) {x y : LevelGroup H}
    (h : ∀ v, IsConj (x v) (y v)) : tupleChar s x = tupleChar s y :=
  Finset.prod_congr rfl fun v _ => (GlobalTheory.TypeCharacterConjugateInverse.typeChar_conj_inv _ K _ (s v)).1 _ _ (h v)

theorem comp_flipAt_mem (om : ∀ i : Fin 2, (ZMod (H.g i))ˣ →* Kˣ) (S : Set (Sq H)) {τ : LevelGroup H → K}
    (hτ : τ ∈ goodTypes om) : τ ∘ flipAt S ∈ goodTypes om := by
  obtain ⟨s, hs, rfl⟩ := hτ
  refine ⟨flipParam S s, fun i => goodAt_flip _ _ _ (fun w => ?_) (hs i), tupleChar_flipParam S s⟩
  by_cases hv : (⟨i, w⟩ : Sq H) ∈ S
  · exact Or.inr (if_pos hv)
  · exact Or.inl (if_neg hv)

end Global

theorem coeff_goodIdem_flip (R : Ranks) (H : Host R) (om : ∀ i : Fin 2, (ZMod (H.g i))ˣ →* ℂˣ) (S : Set (Sq H))
    (x y : LevelGroup H) (h1 : ∀ v ∈ S, IsConj (x v)⁻¹ (y v)) (h2 : ∀ v ∉ S, IsConj (x v) (y v)) :
    (goodIdem om).coeff y = (goodIdem om).coeff x := by
  simp only [goodIdem, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, GlobalTheory.SumWCompare.coeff_centralIdem]
  have inv : ∀ τ : LevelGroup H → ℂ, (τ ∘ flipAt S) ∘ flipAt S = τ := fun τ => by
    funext z; simp [flipAt_flipAt]
  refine Finset.sum_nbij' (fun τ => τ ∘ flipAt S) (fun τ => τ ∘ flipAt S) ?_ ?_ (fun τ _ => inv τ) (fun τ _ => inv τ) ?_
  · intro τ hτ
    exact (Set.Finite.mem_toFinset _).2 (comp_flipAt_mem om S ((Set.Finite.mem_toFinset _).1 hτ))
  · intro τ hτ
    exact (Set.Finite.mem_toFinset _).2 (comp_flipAt_mem om S ((Set.Finite.mem_toFinset _).1 hτ))
  · intro τ hτ
    obtain ⟨s, -, rfl⟩ := (Set.Finite.mem_toFinset _).1 hτ
    have key : tupleChar s y⁻¹ = tupleChar s (flipAt S x⁻¹) := by
      refine tupleChar_congr s fun v => ?_
      by_cases hv : v ∈ S
      · simp only [flipAt, if_pos hv, Pi.inv_apply]
        exact isConj_inv_inv (h1 v hv).symm
      · simp only [flipAt, if_neg hv, Pi.inv_apply]
        exact isConj_inv_inv (h2 v hv).symm
    rw [Function.comp_apply, Function.comp_apply, flipAt_one, key]

end GlobalTheory.GoodIdemFlip
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFiniteFormsGLSpanKilledScalarDeriva
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology

namespace GlobalTheory.HCF

theorem span_formsGL_killed_scalD : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E)))
    (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ)), X.Finite → ∀ N : ℕ,
    ∃ Λ : List ℂ, ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N),
      (Λ.map fun c => scalD E a - algebraMap ℂ (Module.End ℂ (Sm E a)) c).prod φ = 0 := by
  intro E _ _ _ a L W X hX N
  set S : Module.End ℂ (Sm E a) := scalD E a with hS
  set f : ℂ → Module.End ℂ (Sm E a) := fun c => S - algebraMap ℂ (Module.End ℂ (Sm E a)) c with hf
  have hSZ : S ∈ Zalg E a := Central.lie_mem_Zalg 1

  have hpow : ∀ (χ : Module.End ℂ (Sm E a) → ℂ) (φ : Sm E a), CentralNilGL χ N φ → (f (χ S) ^ N) φ = 0 := by
    intro χ φ h
    have key : ∀ n : ℕ, (List.replicate n S).foldr (fun z g => z g - χ z • g) φ = (f (χ S) ^ n) φ := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [List.replicate_succ, List.foldr_cons, ih, pow_succ', Module.End.mul_apply]
        simp [hf, Algebra.algebraMap_eq_smul_one]
    rw [← key]
    exact h _ (List.length_replicate) (fun z hz => by rw [List.eq_of_mem_replicate hz]; exact hSZ)
  have hc : ∀ c d, Commute (f c) (f d) := fun c d =>
    Commute.sub_left (Commute.sub_right (Commute.refl S) (Algebra.commute_algebraMap_right _ _))
      (Commute.sub_right (Algebra.commute_algebraMap_left _ _) (Algebra.commute_algebraMap_left _ _))
  have hcl : ∀ (l : List ℂ) c, Commute (f c) (l.map f).prod := fun l c =>
    Commute.list_prod_right _ _ fun y hy => by
      obtain ⟨d, -, rfl⟩ := List.mem_map.1 hy
      exact hc c d
  let G : (Module.End ℂ (Sm E a) → ℂ) → List ℂ := fun χ => List.replicate N (χ S)
  have main : ∀ (Ls : List (Module.End ℂ (Sm E a) → ℂ)) (φ : Sm E a),
      (∃ χ ∈ Ls, (f (χ S) ^ N) φ = 0) → ((Ls.flatMap G).map f).prod φ = 0 := by
    intro Ls
    induction Ls with
    | nil => intro φ h; simp at h
    | cons χ0 rest ih =>
      intro φ ⟨χ, hχ, h0⟩
      rw [List.flatMap_cons, List.map_append, List.prod_append]
      have hA : ((G χ0).map f).prod = f (χ0 S) ^ N := by
        simp [G, List.map_replicate, List.prod_replicate]
      rcases List.mem_cons.1 hχ with rfl | hr
      · have hcomm : Commute ((G χ).map f).prod ((rest.flatMap G).map f).prod := by
          rw [hA]; exact (hcl _ _).pow_left N
        rw [hcomm.eq, Module.End.mul_apply, hA, h0, map_zero]
      · rw [Module.End.mul_apply, ih φ ⟨χ, hr, h0⟩, map_zero]
  refine ⟨hX.toFinset.toList.flatMap G, fun φ hφ => ?_⟩
  have hsub : formsGL E a L W X N ⊆ (LinearMap.ker ((hX.toFinset.toList.flatMap G).map f).prod : Set (Sm E a)) := by
    intro ψ hψ
    obtain ⟨χ, hχX, hχ⟩ := hψ.2.2.2
    exact LinearMap.mem_ker.2 (main _ ψ ⟨χ, by simpa using hχX, hpow χ ψ hχ⟩)
  exact LinearMap.mem_ker.1 ((Submodule.span_le.2 hsub) hφ)

end GlobalTheory.HCF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentAdeleOfPlacesMulEqSumComponents
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.PlaceIdemSum

open GlobalTheory.CompanionTheory.SaGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem idem_eq_sum (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F)
    (h : IsPlacesIdem S₁ S₂ ε) :
    ε = ∑ w ∈ S₁, (placeMapInf w).inj 1 + ∑ v ∈ S₂, (placeMapFin v).inj 1 := by
  classical
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine adele_ext ?_ (finAdele_ext fun u => ?_)
  · have hfin : ∀ v ∈ S₂, fstA F ((placeMapFin v).inj 1) = 0 := fun v _ => rfl
    have hinf : ∀ w ∈ S₁, fstA F ((placeMapInf w).inj 1) = singleI w 1 := fun w _ => rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_sum, map_sum, Finset.sum_congr rfl hfin, Finset.sum_const_zero, add_zero,
      Finset.sum_congr rfl hinf]
    refine ainf_ext fun u => ?_
    change fstA F ε u = (∑ w ∈ S₁, (singleI w 1 : ∀ u : InfinitePlace F, u.Completion)) u
    refine Eq.trans ?_ (Finset.sum_apply u S₁ (fun w => (singleI w 1 : ∀ u : InfinitePlace F, u.Completion))).symm
    by_cases hu : u ∈ S₁
    · rw [h1 u hu, Finset.sum_eq_single u (fun w _ hw => singleI_ne (Ne.symm hw) 1) (fun h => absurd hu h),
        singleI_self]
    · rw [h2 u hu, Finset.sum_eq_zero fun w hw => singleI_ne (fun e : u = w => hu (e ▸ hw)) 1]
  · have hinf : ∀ w ∈ S₁, sndA F ((placeMapInf w).inj 1) = 0 := fun w _ => rfl
    have hfin : ∀ v ∈ S₂, sndA F ((placeMapFin v).inj 1) = singleV F v 1 := fun v _ => rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_sum, map_sum, Finset.sum_congr rfl hinf, Finset.sum_const_zero, zero_add,
      Finset.sum_congr rfl hfin, map_sum]
    by_cases hu : u ∈ S₂
    · rw [h3 u hu, Finset.sum_eq_single u (fun v _ hv => StrongApprox.evalV_single_ne (Ne.symm hv) 1)
        (fun h => absurd hu h), StrongApprox.evalV_single_same]
    · rw [h4 u hu, Finset.sum_eq_zero fun v hv => StrongApprox.evalV_single_ne (fun e : u = v => hu (e ▸ hv)) 1]

theorem iB_tmul {K : Type} [Field K] [Algebra F K] [TopologicalSpace K] (P : PlaceMap F K) (y : K) (e : E) :
    iB (E := E) P (y ⊗ₜ[F] e) = P.inj y ⊗ₜ[F] e := rfl

theorem iB_map_tmul {K : Type} [Field K] [Algebra F K] [TopologicalSpace K] (P : PlaceMap F K) (x : AF F) (e : E) :
    iB P (Algebra.TensorProduct.map P.proj (AlgHom.id F E) (x ⊗ₜ[F] e)) = (P.inj 1 * x) ⊗ₜ[F] e := by
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, iB_tmul, P.inj_proj]

theorem idem_mul_eq_sum : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε →
    ∀ a : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * a =
      ∑ w ∈ S₁, GlobalTheory.CompanionTheory.SaGen.iB (GlobalTheory.CompanionTheory.SaGen.placeMapInf w)
          (Algebra.TensorProduct.map (GlobalTheory.CompanionTheory.SaGen.placeMapInf w).proj (AlgHom.id F E) a) +
        ∑ v ∈ S₂, GlobalTheory.CompanionTheory.SaGen.iB (GlobalTheory.CompanionTheory.SaGen.placeMapFin v)
          (Algebra.TensorProduct.map (GlobalTheory.CompanionTheory.SaGen.placeMapFin v).proj (AlgHom.id F E) a) := by
  intro F E _ _ _ _ S₁ S₂ ε hε a
  induction a using TensorProduct.induction_on with
  | zero => simp only [mul_zero, map_zero, Finset.sum_const_zero, add_zero]
  | tmul x e =>
    simp only [iB_map_tmul]
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.sum_tmul, ← TensorProduct.sum_tmul,
      ← TensorProduct.add_tmul, ← Finset.sum_mul, ← Finset.sum_mul, ← add_mul, ← idem_eq_sum S₁ S₂ ε hε]
  | add a b ha hb =>
    rw [mul_add, ha, hb]
    simp only [map_add (f := _), Finset.sum_add_distrib]
    abel

end GlobalTheory.PlaceIdemSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentPreservesLatticeHat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.LatLoc

theorem loc_transfer {R : Type} [CommRing R] {n : ℕ} {S : Subring R} (H₀ H₁ : Submodule S (Fin n → R)) (N : ℕ)
    (u : S) (ε : R) (hu : (u : R) * N = ε) (hε : ε * ε = ε) (h : ∀ y ∈ H₀, (N : R) • y ∈ H₁) (z : Fin n → R)
    (hz : (fun a => ε * z a) ∈ H₀) : (fun a => ε * z a) ∈ H₁ := by
  have h1 := H₁.smul_mem u (h _ hz)
  convert h1 using 1
  funext a
  show ε * z a = (u : R) * ((N : R) * (ε * z a))
  rw [← mul_assoc, hu, ← mul_assoc, hε]


end GlobalTheory.LatLoc
end

