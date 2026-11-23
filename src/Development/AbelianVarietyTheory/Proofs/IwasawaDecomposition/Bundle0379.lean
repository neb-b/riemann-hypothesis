module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0375
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0369
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0273
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Formalism.LocalToGlobal.Columns.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0365
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0367
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesEqIffReductionEq
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2.MemChart

section Local

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}

theorem coset_eq_iff_redV (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {a a' : Sp E n}
    (ha : ((qOf P : ℕ) : E) • a ∈ stdAt E n P) (ha' : ((qOf P : ℕ) : E) • a' ∈ stdAt E n P) :
    {z | z - a ∈ stdAt E n P} = {z | z - a' ∈ stdAt E n P} ↔
      redV P (((qOf P : ℕ) : E) • a) = redV P (((qOf P : ℕ) : E) • a') := by
  have hq0 := GlobalTheory.TopStep.qOf_ne_zero (P := P)
  have key : {z | z - a ∈ stdAt E n P} = {z | z - a' ∈ stdAt E n P} ↔ a - a' ∈ stdAt E n P := by
    constructor
    · intro h
      have h0 : a ∈ {z | z - a ∈ stdAt E n P} := by
        show a - a ∈ stdAt E n P
        rw [sub_self]
        exact zero_mem _
      rw [h] at h0
      exact h0
    · intro h
      ext z
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hz
        have := add_mem hz h
        rwa [sub_add_sub_cancel] at this
      · intro hz
        have := sub_mem hz h
        rwa [sub_sub_sub_cancel_right] at this
  rw [key, GlobalTheory.TopStep.mem_stdAt]
  constructor
  · intro h
    funext i
    have hi := GlobalTheory.TopStep.mem_stdAt.1 ha i
    have hi' := GlobalTheory.TopStep.mem_stdAt.1 ha' i
    show redP P ((((qOf P : ℕ) : E) • a) i) = redP P ((((qOf P : ℕ) : E) • a') i)
    rw [← sub_eq_zero, ← GlobalTheory.TopStep.reduction_sub hi hi']
    apply GlobalTheory.TopStep.redP_eq_zero_of_div
    convert h i using 1
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    field_simp
  · intro h i
    have hi := GlobalTheory.TopStep.mem_stdAt.1 ha i
    have hi' := GlobalTheory.TopStep.mem_stdAt.1 ha' i
    have e := congrFun h i
    have h0 : redP P ((((qOf P : ℕ) : E) • a) i - (((qOf P : ℕ) : E) • a') i) = 0 := by
      rw [GlobalTheory.TopStep.reduction_sub hi hi']
      exact sub_eq_zero.2 e
    have := GlobalTheory.TopStep.intAt_div_of_redP hq (GlobalTheory.TopStep.intAt_sub hi hi') h0
    convert this using 1
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    field_simp

end Local

section Pt

open Classical

variable {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}

theorem mem_vGs_of_rowSG (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (P : rowSG Pr sel mu) : P.1 ∈ Pr.vGs := by
  have h := P.2
  simp only [rowSG, uSG, hQ, Finset.union_empty] at h
  exact h

theorem ptAt_coset (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (q : PtAt R sel mu cst u j) (h : j + 1 = R.m) :
    ∃ y : Sp X.E (R.N j), (∀ w ∈ Pr.vGs, ((qOf w : ℕ) : X.E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N) ∧
      ∀ z, z ∈ q.1.2 ↔ ∀ w ∈ Pr.vGs, z - y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N := by
  obtain ⟨y, hy, hY⟩ := q.mem_ybSet h
  refine ⟨y, fun w hw => ?_, fun z => ?_⟩
  · have := (Formalism.L2.Col.mem_locLat _ _ _ _).1 hy ⟨w, Finset.mem_union_left _ hw⟩
    simpa [hw] using this
  · rw [hY, Set.mem_setOf_eq, Formalism.L2.Col.mem_locLat]
    constructor
    · intro h w hw
      simpa [hw] using h ⟨w, Finset.mem_union_left _ hw⟩
    · intro h P
      have hP := mem_vGs_of_rowSG hQ P
      simpa [hP] using h P.1 hP

theorem cosetIn_eq (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (q : PtAt R sel mu cst u j) {y : Sp X.E (R.N j)}
    (hY : ∀ z, z ∈ q.1.2 ↔ ∀ w ∈ Pr.vGs, z - y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N) (P : rowSG Pr sel mu) :
    cosetIn q P = {z | z - (q.1.1.deco.1.liftFr ⟨P.1, mem_vGs_of_rowSG hQ P⟩).symm y ∈ stdAt X.E (R.N j) P.1} := by
  have hP := mem_vGs_of_rowSG hQ P
  have hf := GlobalTheory.TopStep.liftFr_spec q.1.1.deco.2 ⟨P.1, hP⟩
  have hfr : frsF sel mu q.1.1 P = q.1.1.deco.1.liftFr ⟨P.1, hP⟩ := by
    unfold frsF
    rw [dite_eq_left hP]
  ext z
  simp only [cosetIn, Set.mem_setOf_eq, if_pos hP, pow_zero, inv_one, one_smul, hfr]
  constructor
  · rintro ⟨y', hy', hz⟩
    have h1 : (q.1.1.deco.1.liftFr ⟨P.1, hP⟩).symm y' - (q.1.1.deco.1.liftFr ⟨P.1, hP⟩).symm y ∈ stdAt X.E (R.N j) P.1 := by
      rw [← map_sub]
      exact (hf.1 _).1 (by rw [LinearEquiv.apply_symm_apply]; exact (hY y').1 hy' P.1 hP)
    have := add_mem hz h1
    rwa [sub_add_sub_cancel] at this
  · intro hz
    exact ⟨y, (hY y).2 fun w _ => by rw [sub_self]; exact zero_mem _, hz⟩

theorem bar_eq (q : PtAt R sel mu cst u j) {y : Sp X.E (R.N j)}
    (hy : ∀ w ∈ Pr.vGs, ((qOf w : ℕ) : X.E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N)
    (hY : ∀ z, z ∈ q.1.2 ↔ ∀ w ∈ Pr.vGs, z - y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N) (w : Pr.vGs) :
    bar q w = {redV w.1 (((qOf w.1 : ℕ) : X.E) • (q.1.1.deco.1.liftFr w).symm y)} := by
  have hd := q.1.1.deco.2
  have hf := GlobalTheory.TopStep.liftFr_spec hd w
  have hq := hy w.1 w.2
  have key : q.1.1.deco.1.be w (((qOf w.1 : ℕ) : X.E) • y) =
      redV w.1 (((qOf w.1 : ℕ) : X.E) • (q.1.1.deco.1.liftFr w).symm y) := by
    rw [← map_smul]
    have hs : (q.1.1.deco.1.liftFr w).symm (((qOf w.1 : ℕ) : X.E) • y) ∈ stdAt X.E _ w.1 :=
      (hf.1 _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hq)
    rw [← hf.2 _ hs, LinearEquiv.apply_symm_apply]
  ext v
  simp only [bar, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← key]
    have ht : z - y ∈ q.1.1.deco.1.at w.1 := (hY z).1 hz w.1 w.2
    have e : ((qOf w.1 : ℕ) : X.E) • z = ((qOf w.1 : ℕ) : X.E) • y + ((qOf w.1 : ℕ) : X.E) • (z - y) := by
      rw [← smul_add, add_sub_cancel]
    rw [e, hd.be_add w _ hq _ (GlobalTheory.TopStep.smul_mem_locP (GlobalTheory.TopStep.intAt_nat _) ht),
      GlobalTheory.TopStep.be_smul_int hd w (GlobalTheory.TopStep.intAt_nat _) ht, GlobalTheory.TopStep.reduction_absNorm_eq_zero, zero_smul, add_zero]
  · rintro rfl
    exact ⟨y, (hY y).2 fun w _ => by rw [sub_self]; exact zero_mem _, key.symm⟩

theorem cosetIn_eq_iff_bar_eq : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ},
    QE sel (mu : Chr X.F X.E X.K) = ∅ → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) →
    ∀ q q' : PtAt R sel mu cst u j, cosetIn q = cosetIn q' ↔ MemChart.bar q = MemChart.bar q' := by
  intro X Pr R sel S mu cst u j hQ hq q q'
  by_cases h : j + 1 = R.m
  · obtain ⟨y, hy, hY⟩ := ptAt_coset hQ q h
    obtain ⟨y', hy', hY'⟩ := ptAt_coset hQ q' h
    have hA : ∀ (p : PtAt R sel mu cst u j) (y : Sp X.E (R.N j)),
        (∀ w ∈ Pr.vGs, ((qOf w : ℕ) : X.E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal p.1.1.deco.1.N) → ∀ w : Pr.vGs,
        ((qOf w.1 : ℕ) : X.E) • (p.1.1.deco.1.liftFr w).symm y ∈ stdAt X.E (R.N j) w.1 := by
      intro p y hy w
      have hf := GlobalTheory.TopStep.liftFr_spec p.1.1.deco.2 w
      rw [← map_smul]
      exact (hf.1 _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hy w.1 w.2)
    rw [funext_iff, funext_iff]
    constructor
    · intro H w
      have := H ⟨w.1, Finset.mem_union_left _ w.2⟩
      rw [cosetIn_eq hQ q hY, cosetIn_eq hQ q' hY'] at this
      rw [bar_eq q hy hY, bar_eq q' hy' hY', Set.singleton_eq_singleton_iff]
      exact (coset_eq_iff_redV (hq w.1 w.2) (hA q y hy w) (hA q' y' hy' w)).1 this
    · intro H P
      have hP := mem_vGs_of_rowSG hQ P
      have := H ⟨P.1, hP⟩
      rw [bar_eq q hy hY, bar_eq q' hy' hY', Set.singleton_eq_singleton_iff] at this
      rw [cosetIn_eq hQ q hY, cosetIn_eq hQ q' hY']
      exact (coset_eq_iff_redV (hq P.1 hP) (hA q y hy ⟨P.1, hP⟩) (hA q' y' hy' ⟨P.1, hP⟩)).2 this
  · have e : ∀ p : PtAt R sel mu cst u j, p.1.2 = ∅ := fun p => by
      have := p.2
      rw [ysAt_ys_of_ne sel mu cst h] at this
      exact this
    have h1 : ∀ p : PtAt R sel mu cst u j, cosetIn p = fun _ => ∅ := fun p => by
      funext P
      ext z
      simp [cosetIn, e p]
    have h2 : ∀ p : PtAt R sel mu cst u j, bar p = fun _ => ∅ := fun p => by
      funext w
      ext v
      simp [bar, e p]
    rw [h1 q, h1 q', h2 q, h2 q']
    simp

end Pt

end GlobalTheory.Mem.Col2.MemChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspParamOfGreenParametrisation
section
noncomputable section

open CategoryTheory Polynomial Formalism.L2.NT

namespace GlobalTheory.GreenParam

open GlobalTheory.GLq GlobalTheory.GLq.LabelUnique Formalism.IrreducibleCountingLemmas.TYPES

variable {g : ℕ} [Fact g.Prime]

def datum (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y)
    (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) (hζ : IsGenSys ζ) : LabelDatum g where
  teich := t
  teich_inj := ht
  gen := ζ
  gen_order d hd := (hζ d hd).1
  gen_norm d e hd he := (hζ d hd).2 (d * e) (dvd_mul_right d e) (Nat.mul_pos hd he)

theorem mem_rootsBar_of_aeval {P : (ZMod g)[X]} (hP : P ≠ 0) {x : Formalism.CyclotomicNorms.Fbar g}
    (hx : aeval x P = 0) : x ∈ Formalism.CyclotomicNorms.rootsBar P := by
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [mem_roots (Polynomial.map_ne_zero hP), IsRoot, Polynomial.eval_map, ← aeval_def]
  exact hx

theorem isPrimeLab_iff (d : ℕ) (P : (ZMod g)[X]) :
    IsPrimeLab d P ↔ P.Monic ∧ Irreducible P ∧ P ≠ X ∧ P.natDegree = d := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, ?_, h4⟩
    rintro rfl
    exact h3 (by simp)
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, fun h0 => h3 ?_, h4⟩
    have hd : (X : (ZMod g)[X]) ∣ P := X_dvd_iff.2 h0
    exact (eq_of_monic_of_associated monic_X h1 (irreducible_X.associated_of_dvd h2 hd)).symm

theorem isPrimeLab_charpoly {d : ℕ} (y : Gn g d) (hy : Irreducible (y : Mt g d).charpoly) :
    IsPrimeLab d (y : Mt g d).charpoly := by
  refine ⟨Matrix.charpoly_monic _, hy, fun h0 => ?_, by simp [Matrix.charpoly_natDegree_eq_dim]⟩
  have hdet := Matrix.det_eq_sign_charpoly_coeff (y : Mt g d)
  rw [h0, mul_zero] at hdet
  exact (Matrix.isUnits_det_units y).ne_zero hdet

theorem exists_gen_pow (L : LabelDatum g) {d : ℕ} (hd : 0 < d) {z : Formalism.CyclotomicNorms.Fbar g}
    (hz : z ^ (g ^ d - 1) = 1) : ∃ m : ℕ, L.gen d ^ m = z := by
  have h1 : 1 < g ^ d := Nat.one_lt_pow hd.ne' (Fact.out : g.Prime).one_lt
  haveI : NeZero (g ^ d - 1) := ⟨by omega⟩
  have hp : IsPrimitiveRoot (L.gen d) (g ^ d - 1) := by
    rw [← L.gen_order d hd]; exact IsPrimitiveRoot.orderOf _
  obtain ⟨m, -, hm⟩ := hp.eq_pow_of_pow_eq_one hz
  exact ⟨m, hm⟩

theorem sum_thetaOf (L : LabelDatum g) {d : ℕ} (hd : 0 < d) {P : (ZMod g)[X]} (hP : IsPrimeLab d P)
    {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ∈ Formalism.CyclotomicNorms.rootsBar P) (m : ℕ) :
    ∑ i ∈ Finset.range d, thetaOf L d x ((L.gen d ^ m) ^ (g ^ i)) =
      ∑ i ∈ Finset.range d, L.teich x ^ (m * g ^ i) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have hw : L.teich x ^ (g ^ d - 1) = 1 := by rw [← map_pow, pow_sub_one_eq_one hP hx, map_one]
  rw [← pow_mul, thetaOf_gen_pow L d hd x hw]

theorem hasCuspLabel_iff (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y)
    (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) (hζ : IsGenSys ζ) {d : ℕ} (V : FDRep ℂ (GL (Fin d) (ZMod g)))
    (hV : IsCusp (fun x => V.character x)) (P : (ZMod g)[X]) :
    HasCuspLabel (convC t ht ζ hζ) V P ↔ IsCuspOf (datum t ht ζ hζ) P (fun x => V.character x) := by
  have hd : 0 < d := hV.1
  unfold HasCuspLabel
  simp only [Fintype.card_fin, ZMod.card]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    have hP : IsPrimeLab d P := (isPrimeLab_iff d P).2 ⟨h1, h2, h3, h4⟩
    refine ⟨hP, hV, fun x hx y hy z hz => ?_⟩
    have hy' := isPrimeLab_charpoly y hy
    obtain ⟨m, rfl⟩ := exists_gen_pow (datum t ht ζ hζ) hd (pow_sub_one_eq_one hy' hz)
    rw [sum_thetaOf _ hd hP hx]
    exact h5 x (aeval_eq_zero_of_mem h1.ne_zero hx) y hy _ (aeval_eq_zero_of_mem hy.ne_zero hz) m rfl
  · rintro ⟨hP, -, h5⟩
    obtain ⟨h1, h2, h3, h4⟩ := (isPrimeLab_iff d P).1 hP
    refine ⟨h1, h2, h3, h4, fun x hx y hy z hz m hm => ?_⟩
    have hx' := mem_rootsBar_of_aeval h1.ne_zero hx
    have h := h5 x hx' y hy z (mem_rootsBar_of_aeval hy.ne_zero hz)
    have hm' : (datum t ht ζ hζ).gen d ^ m = z := hm
    rw [← hm', sum_thetaOf _ hd hP hx'] at h
    exact h

theorem nonempty_iso_of_character {G : Type} [Group G] [Fintype G] (V W : FDRep ℂ G) [Simple V] [Simple W]
    (h : V.character = W.character) : Nonempty (V ≅ W) := by
  haveI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  haveI : Invertible (Fintype.card G : ℂ) := invertibleOfNonzero (by exact_mod_cast Fintype.card_pos.ne')
  have h1 := FDRep.char_orthonormal V W
  have h2 := FDRep.char_orthonormal V V
  rw [← h, h2, if_pos ⟨Iso.refl V⟩] at h1
  by_contra h3
  rw [if_neg h3] at h1
  exact one_ne_zero h1

theorem cuspParam_of_green : GlobalTheory.Published.GreenCuspidal → ∀ (g : ℕ) [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g)
    (hζ : IsGenSys ζ), Formalism.IrreducibleCountingLemmas.TYPES.CuspParam (ZMod g) (convC t ht ζ hζ) := by
  intro hG g _ t ht ζ hζ d hd
  obtain ⟨τ, hτ, -, hall⟩ := hG g (datum t ht ζ hζ) d hd
  have huniq := GlobalTheory.GLq.LabelUniqueAll.label_eq (datum t ht ζ hζ) d
  refine ⟨fun V hs hc => ?_, fun P h1 h2 h3 h4 => ?_, fun V W P hs hc hs' hc' hP hP' => ?_⟩
  · have hV := (_root_.GlobalTheory.CuspCharRep.isCusp_character_iff_isCuspidal g d V hd hs).2 hc
    obtain ⟨Q, hQ, hVQ⟩ := hall _ hV
    refine ⟨⟨Q, ?_, fun P hP => ?_⟩, ?_⟩
    · refine (hasCuspLabel_iff t ht ζ hζ V hV Q).2 ?_
      rw [hVQ]; exact (hτ Q hQ).1
    · refine huniq P Q _ ((hasCuspLabel_iff t ht ζ hζ V hV P).1 hP) ?_
      rw [hVQ]; exact (hτ Q hQ).1
    · have h1 : V.character 1 = τ Q 1 := congrFun hVQ 1
      rw [FDRep.char_one, (hτ Q hQ).2] at h1
      simp only [q, ZMod.card]
      exact_mod_cast h1
  · have hP : IsPrimeLab d P := (isPrimeLab_iff d P).2 ⟨h1, h2, h3, h4⟩
    have hc := (hτ P hP).1
    obtain ⟨V, hs, hVχ⟩ := hc.2.1.2.1
    have he : (fun x => V.character x) = τ P := funext hVχ
    have hV : IsCusp (fun x => V.character x) := he ▸ hc.2.1
    exact ⟨V, hs, (_root_.GlobalTheory.CuspCharRep.isCusp_character_iff_isCuspidal g d V hd hs).1 hV, (hasCuspLabel_iff t ht ζ hζ V hV P).2 (he ▸ hc)⟩
  · have hV := (_root_.GlobalTheory.CuspCharRep.isCusp_character_iff_isCuspidal g d V hd hs).2 hc
    have hW := (_root_.GlobalTheory.CuspCharRep.isCusp_character_iff_isCuspidal g d W hd hs').2 hc'
    obtain ⟨Q, hQ, hVQ⟩ := hall _ hV
    obtain ⟨Q', hQ', hWQ⟩ := hall _ hW
    have e1 : P = Q := huniq P Q _ ((hasCuspLabel_iff t ht ζ hζ V hV P).1 hP) (hVQ ▸ (hτ Q hQ).1)
    have e2 : P = Q' := huniq P Q' _ ((hasCuspLabel_iff t ht ζ hζ W hW P).1 hP') (hWQ ▸ (hτ Q' hQ').1)
    refine nonempty_iso_of_character V W ?_
    exact hVQ.trans ((e1.symm.trans e2) ▸ hWQ.symm)

end GlobalTheory.GreenParam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicPointDecoratedLatticeAllTwists
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.PtTwist

open GlobalTheory.Mem.Col2.PtExist

theorem exists_ptOf_twists : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (n : ℕ)
    (p : DecoF B.fields.E n ((B.primes X).vT u) (B.primes X).vGs I.SQ), ∃ g : GA B n, PtOf g p := by
  classical
  intro B X I hI u n p
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
  obtain ⟨hlev, hGQ, -⟩ := GlobalTheory.Mem.LevTwist.levOk_twists B X I hI
  have hT0 : (B.primes X).piT u ≠ 0 := fun h => by
    have := hPr.piT_norm u
    rw [h, zero_mul] at this
    exact (hPr.T_prime u).ne_zero (Nat.cast_eq_zero.1 this.symm)

  have hTin : ∀ P ∈ (B.primes X).vT u, (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal := fun P hP => by
    have h1 : (B.primes X).piT u ∈ P.asIdeal := (mem_divs hT0 P).1 hP
    rw [← hPr.piT_norm u]
    exact Ideal.mul_mem_right _ _ h1

  have hcj : ∀ (P : HeightOneSpectrum (𝓞 B.fields.E)) (m : ℕ),
      ((m : ℕ) : 𝓞 B.fields.E) ∈ (conjPrime₂ P).asIdeal ↔ ((m : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal := fun P m => by
    rw [mem_conjP, map_natCast]

  have hG : ∀ P ∈ (B.primes X).vGs, (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∉ P.asIdeal := fun P hP =>
    T_notMem_vGs hPr u ⟨P, hP⟩

  have hQ : ∀ P ∈ I.SQ, (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∉ P.asIdeal := fun P hP h => by
    have hg := (GlobalTheory.Mem.LevTwist.good_of_mem hI hP).2
    have e := (ReadTwist.plc_under_eq_iff (F := B.host.F) P (hPr.T_prime u)).2 h
    refine hg.2.2 ?_
    rw [e]
    exact hI.T_mem u
  have hTG : Disjoint ((B.primes X).vT u) (B.primes X).vGs :=
    Finset.disjoint_left.2 fun P h1 h2 => hG P h2 (hTin P h1)
  have hTQ : Disjoint ((B.primes X).vT u) I.SQ :=
    Finset.disjoint_left.2 fun P h1 h2 => hQ P h2 (hTin P h1)
  have hout : ∀ P ∈ uSG (B.primes X).vGs I.SQ, (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∉ P.asIdeal := fun P hP => by
    rcases Finset.mem_union.1 hP with h | h
    exacts [hG P h, hQ P h]
  refine PtExist.exists_isPtOf_cm _ n _ _ _ p hTG hTQ hGQ fun P hP hP' => ?_
  rcases Finset.mem_union.1 hP with h1 | h1 <;> rcases Finset.mem_union.1 hP' with h2 | h2
  ·
    have a1 : (B.primes X).piT u ∈ P.asIdeal := (mem_divs hT0 P).1 h1
    have a2 : (B.primes X).piT u ∈ (conjPrime₂ P).asIdeal := (mem_divs hT0 _).1 h2
    rw [mem_conjP] at a2
    obtain ⟨a, b, hab⟩ := hPr.piT_cop u
    have : (1 : 𝓞 B.fields.E) ∈ P.asIdeal := by
      rw [← hab]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ a1) (Ideal.mul_mem_left _ _ a2)
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
  · exact hout _ h2 ((hcj P _).2 (hTin P h1))
  · exact hout P h1 ((hcj P _).1 (hTin _ h2))
  · exact hlev.split P h1 h2

end GlobalTheory.Mem.Col2.PtTwist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefficientFieldContainsHeckeEigenvalues
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.HFld

theorem heckeFields_of (hF : ∀ (P : Pre) (f : Top.Fr P) (F F₀ : IntermediateField ℚ ℂ) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)),
  ∃ (n : ℕ) (Wt : Fin n → Σ B0 : Base, Σ px0 : PreX B0.toPre, Col2.ColIn B0 px0),
    (∀ i, (Wt i).1.fields.Ok ∧ (Wt i).2.2.Ok) ∧
    ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px), B.fields.Ok → I.Ok → B.toPre = P → HEq I.C f → B.KsC = F →
      B.fixedCoefficientFieldInComplex = F₀ → HEq (Set.range I.xi) Ξ → ∃ i, GlobalTheory.Mem.HFld.SameCfg B px I (Wt i).1 (Wt i).2.1 (Wt i).2.2) (hT : ∀ (B0 : Base) (px0 : PreX B0.toPre) (I0 : Col2.ColIn B0 px0), B0.fields.Ok → I0.Ok →
  ∃ s : Finset ℂ, (∀ z ∈ s, IsAlgebraic ℚ z) ∧
    ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px), B.fields.Ok → I.Ok → GlobalTheory.Mem.HFld.SameCfg B px I B0 px0 I0 →
      (∀ z ∈ s, z ∈ B.LLC) → ∀ a : I.ι,
        Formalism.L2.Col.HeckeFieldsInAll (rowPts B.wts I.Ch I.sel (I.tup a)) ∅ ∧
          ∀ j : Fin B.R.m, Formalism.L2.Col.HeckeFieldsInAll (liftPts B.wts I.Ch I.sel (I.tup a) (j.1 + 1)) ∅) :
    ∃ So : ∀ P : Pre, Top.Fr P → IntermediateField ℚ ℂ → IntermediateField ℚ ℂ → Set (Formalism.L2.Host.HChar P.host.E) → Finset ℂ,
  (∀ P f F F₀ Ξ, ∀ z ∈ So P f F F₀ Ξ, IsAlgebraic ℚ z) ∧
  ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px), B.fields.Ok → I.Ok →
    (∀ z ∈ So B.toPre I.C B.KsC B.fixedCoefficientFieldInComplex (Set.range I.xi), z ∈ B.LLC) → ∀ a : I.ι,
      Formalism.L2.Col.HeckeFieldsInAll (rowPts B.wts I.Ch I.sel (I.tup a)) ∅ ∧
        ∀ j : Fin B.R.m, Formalism.L2.Col.HeckeFieldsInAll (liftPts B.wts I.Ch I.sel (I.tup a) (j.1 + 1)) ∅ := by
  classical
  choose n Wt hWok hWcov using hF
  choose s hsalg hs using hT
  refine ⟨fun P f F F₀ Ξ => Finset.univ.biUnion fun i : Fin (n P f F F₀ Ξ) =>
    s (Wt P f F F₀ Ξ i).1 (Wt P f F F₀ Ξ i).2.1 (Wt P f F F₀ Ξ i).2.2 (hWok P f F F₀ Ξ i).1 (hWok P f F F₀ Ξ i).2, ?_, ?_⟩
  · intro P f F F₀ Ξ z hz
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hz
    exact hsalg _ _ _ _ _ z hi
  · intro B px I hB hI hS a
    obtain ⟨i, hi⟩ := hWcov B.toPre I.C B.KsC B.fixedCoefficientFieldInComplex (Set.range I.xi) B px I hB hI rfl HEq.rfl rfl rfl HEq.rfl
    exact hs _ _ _ _ _ B px I hB hI hi (fun z hz => hS z (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hz⟩)) a

theorem heckeFields :
    ∃ So : ∀ P : Pre, Top.Fr P → IntermediateField ℚ ℂ → IntermediateField ℚ ℂ → Set (Formalism.L2.Host.HChar P.host.E) → Finset ℂ,
  (∀ P f F F₀ Ξ, ∀ z ∈ So P f F F₀ Ξ, IsAlgebraic ℚ z) ∧
  ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px), B.fields.Ok → I.Ok →
    (∀ z ∈ So B.toPre I.C B.KsC B.fixedCoefficientFieldInComplex (Set.range I.xi), z ∈ B.LLC) → ∀ a : I.ι,
      Formalism.L2.Col.HeckeFieldsInAll (rowPts B.wts I.Ch I.sel (I.tup a)) ∅ ∧
        ∀ j : Fin B.R.m, Formalism.L2.Col.HeckeFieldsInAll (liftPts B.wts I.Ch I.sel (I.tup a) (j.1 + 1)) ∅ :=
  heckeFields_of _root_.GlobalTheory.Mem.HFld.exists_finite_cfg _root_.GlobalTheory.Mem.HFld.Transp.transp

end GlobalTheory.Mem.HFld

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalComponentConjSplitPlaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localComponent_conj_splitPlace : ∀ (D : D7) (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E) (w : PlE D.host),
    IsConjPl D.host w s.w → ∃ x, GlobalTheory.AutQuot.LocAt π w x := by
  first | exact @GlobalTheory.AutQuot.conjLoc | exact GlobalTheory.AutQuot.conjLoc | (intros; apply GlobalTheory.AutQuot.conjLoc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdentityIntegralUnitaryFrameCoordinatesOfUnitGraStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.identity_integralUnitaryFrameCoordinates_of_unitGram : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (i : Fin X.toD7.R.m) (t : TupU I U), (Vc X.toD7 i).gram = 1 → LiftBrg.FrameOK X I U i t 1 1 := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.frameOK_one_of_gram_eq_one | exact GlobalTheory.Mem.R3.LiftBrg.frameOK_one_of_gram_eq_one | (intros; apply GlobalTheory.Mem.R3.LiftBrg.frameOK_one_of_gram_eq_one <;> assumption)
end

