module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1515
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorRationalTranslateMemThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalCoordinatesGroupLaw
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem crdLaw_cT_mul {A : Type} [CommRing A] (s : A →+* A) {a b c : Type} [Fintype b] (M : Matrix a b A) (N : Matrix b c A) :
    cT s (M * N) = cT s N * cT s M := by
  simp [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem crdLaw_cT_add {A : Type} [CommRing A] (s : A →+* A) {a b : Type} (M N : Matrix a b A) :
    cT s (M + N) = cT s M + cT s N := by
  simp [cT, Matrix.map_add (f := _), Matrix.transpose_add]

theorem crdLaw_cT_one {A : Type} [CommRing A] (s : A →+* A) {a : Type} [DecidableEq a] :
    cT s (1 : Matrix a a A) = 1 := by
  simp [cT]

theorem crdLaw_plus_add {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {j m : ℕ} (J₀ : Matrix (Fin m) (Fin m) E) (b b' : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) :
    plus σ J₀ (b + b') = plus σ J₀ b + plus σ J₀ b' := by
  simp only [plus, crdLaw_cT_add, Matrix.mul_add]

theorem crdLaw_plus_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {j m : ℕ} (J₀ : Matrix (Fin m) (Fin m) E) (a : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) :
    plus σ J₀ (a * b) = plus σ J₀ b * cT (sigR (AF F) σ) a := by
  simp only [plus, crdLaw_cT_mul, Matrix.mul_assoc]

theorem crd_law : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ (u u' : GAd σ J) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) (b' : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c' : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), Crd σ J C D Z J₀ u b c → (Crd σ J C D Z J₀ u' b' c' → Crd σ J C D Z J₀ (u * u') (b + b') (c + c' - b * plus σ J₀ b')) ∧ (Crd σ J C D Z J₀ u' b c → u = u') ∧ ∀ α, Crd σ J C D Z J₀ (lv α * u * (lv α)⁻¹) (α.1 * b) (α.1 * c * cT (sigR (AF F) σ) α.1) := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF lv hL u u' b c b' c' h
  refine ⟨fun h' => ?_, fun h' => ?_, fun α => ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · rw [map_mul, Units.val_mul, Matrix.mul_assoc, h'.onC, h.onC]
    · rw [map_mul, Units.val_mul, Matrix.mul_assoc, h'.onZ, Matrix.mul_add, h.onZ, ← Matrix.mul_assoc, h.onC,
        Matrix.mul_add, add_assoc]
    · have eZ : (matHom _ σ J u).1 * (adMat F Z * plus σ J₀ b') = (adMat F Z + adMat F C * b) * plus σ J₀ b' := by
        rw [← Matrix.mul_assoc, h.onZ]
      have eC : (matHom _ σ J u).1 * (adMat F C * c') = adMat F C * c' := by
        rw [← Matrix.mul_assoc, h.onC]
      rw [map_mul, Units.val_mul, Matrix.mul_assoc, h'.onD, Matrix.mul_add, Matrix.mul_sub, h.onD, eZ, eC,
        crdLaw_plus_add]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_assoc]
      abel
  · exact eq_of_frame_cols F E σ n J j m C D Z J₀ hF u u' (h.onC.trans h'.onC.symm) (h.onZ.trans h'.onZ.symm)
      (h.onD.trans h'.onD.symm)
  · have hinv : (lv α)⁻¹ = lv α⁻¹ := (map_inv lv α).symm
    have iC : (matHom _ σ J (lv α⁻¹)).1 * adMat F C = adMat F C * (α⁻¹).1 := hL.onC α⁻¹
    have iZ : (matHom _ σ J (lv α⁻¹)).1 * adMat F Z = adMat F Z := hL.onZ α⁻¹
    have iD : (matHom _ σ J (lv α⁻¹)).1 * adMat F D = adMat F D * cT (sigR (AF F) σ) α.1 := by
      rw [hL.onD α⁻¹, inv_inv]
    have one : cT (sigR (AF F) σ) (α⁻¹).1 * cT (sigR (AF F) σ) α.1 = 1 := by
      rw [← crdLaw_cT_mul, Units.mul_inv, crdLaw_cT_one]
    have aC : (matHom _ σ J (lv α)).1 * (adMat F C * b) = adMat F C * (α.1 * b) := by
      rw [← Matrix.mul_assoc, hL.onC, Matrix.mul_assoc]
    rw [hinv]
    refine ⟨?_, ?_, ?_⟩
    · rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, iC, ← Matrix.mul_assoc,
        Matrix.mul_assoc _ _ (adMat F C), h.onC, hL.onC, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    · rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, iZ, Matrix.mul_assoc, h.onZ,
        Matrix.mul_add, hL.onZ, aC]
    · rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, iD, Matrix.mul_assoc,
        ← Matrix.mul_assoc _ (adMat F D), h.onD, crdLaw_plus_mul]
      have eZ : (matHom _ σ J (lv α)).1 * (adMat F Z * plus σ J₀ b) = adMat F Z * plus σ J₀ b := by
        rw [← Matrix.mul_assoc, hL.onZ]
      have eC : (matHom _ σ J (lv α)).1 * (adMat F C * c) = adMat F C * (α.1 * c) := by
        rw [← Matrix.mul_assoc, hL.onC, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_sub, hL.onD, eZ, eC]
      simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, one, Matrix.mul_one]

end GlobalTheory.SphEis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCongruentOneDetSubOneMemIdealMulConj
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.StdDatum.DetCong

variable {D : D7}

theorem inc_mul_mem_hatId {I J : Ideal (𝓞 D.host.E)} {b : 𝓞 D.host.E} (hb : b ∈ I) {y : AE D}
    (hy : y ∈ hatId D J) : inc D (b : D.host.E) * y ∈ hatId D (I * J) := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, s, hs, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨b * c, Ideal.mul_mem_mul hb hc, s, hs, ?_⟩
    rw [← mul_assoc, ← map_mul]; rfl
  | zero => rw [mul_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg _ _ h => rw [mul_neg]; exact neg_mem h

theorem sgA_mem_hatId {𝔪 : Ideal (𝓞 D.host.E)} {y : AE D} (hy : y ∈ hatId D 𝔪) :
    sgA D y ∈ hatId D (D.host.conj • 𝔪) := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, s, hs, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨D.host.conj • c, Ideal.smul_mem_pointwise_smul _ _ _ hc, sgA D s,
      VacMove.sgA_mem D hs, ?_⟩
    rw [map_mul, GlobalTheory.NormSum.PtsMem.sgA_inc]; rfl
  | zero => rw [map_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | neg _ _ h => rw [map_neg]; exact neg_mem h

theorem prod_sub_prod_mem {𝔪 : Ideal (𝓞 D.host.E)} {ι : Type*} (s : Finset ι) (f g : ι → AE D)
    (hf : ∀ i ∈ s, f i ∈ OhE D) (hg : ∀ i ∈ s, g i ∈ OhE D) (h : ∀ i ∈ s, f i - g i ∈ hatId D 𝔪) :
    (∏ i ∈ s, f i) - ∏ i ∈ s, g i ∈ hatId D 𝔪 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, sub_self]; exact zero_mem _
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have e : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i =
        f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i := by ring
    rw [e]
    refine add_mem (mul_mem_hatId (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) (fun i hi => hg i (Finset.mem_insert_of_mem hi))
        (fun i hi => h i (Finset.mem_insert_of_mem hi))))
      (mem_hatId_mul (prod_mem fun i hi => hg i (Finset.mem_insert_of_mem hi)) (h a (Finset.mem_insert_self a s)))

theorem det_sub_one_mem_hatId_of {𝔪 : Ideal (𝓞 D.host.E)} {a : ℕ} (M : Matrix (Fin a) (Fin a) (AE D))
    (hM : ∀ i j, M i j ∈ OhE D) (hC : ∀ i j, (M - 1) i j ∈ hatId D 𝔪) : M.det - 1 ∈ hatId D 𝔪 := by
  have h1 : ∀ i j, (1 : Matrix (Fin a) (Fin a) (AE D)) i j ∈ OhE D := fun i j => by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  rw [← Matrix.det_one (R := AE D) (n := Fin a), Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
  refine sum_mem fun σ _ => ?_
  rw [← smul_sub]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h]
  · rw [one_smul]
    exact prod_sub_prod_mem _ _ _ (fun i _ => hM _ _) (fun i _ => h1 _ _) (fun i _ => hC _ _)
  · rw [Units.neg_smul, one_smul]
    exact neg_mem (prod_sub_prod_mem _ _ _ (fun i _ => hM _ _) (fun i _ => h1 _ _) (fun i _ => hC _ _))

theorem det_sub_one_mem : ∀ (D : D7) {a : ℕ} (𝔪 : Ideal (𝓞 D.host.E)), IsCoprime 𝔪 (D.host.conj • 𝔪) →
    ∀ k : GA D a, k ∈ intG D a → CongOne D 𝔪 k →
      ((Matrix.GeneralLinearGroup.det (k : GL (Fin a) (AE D)) : (AE D)ˣ) : AE D) - 1 ∈
        hatId D (𝔪 * D.host.conj • 𝔪) := by
  intro D a 𝔪 hco k hk hc
  set u : AE D := ((Matrix.GeneralLinearGroup.det (k : GL (Fin a) (AE D)) : (AE D)ˣ) : AE D) with hu
  have hint := (mem_intG k).1 hk
  have huO : u ∈ OhE D := VacMove.det_int D _ hint
  have h1 : u - 1 ∈ hatId D 𝔪 := by
    rw [hu, Matrix.GeneralLinearGroup.val_det_apply]
    exact det_sub_one_mem_hatId_of _ (fun i j => (hint i j).1) hc
  have hn : u * sgA D u = 1 := VacMove.det_norm D k
  have h2 : u - 1 ∈ hatId D (D.host.conj • 𝔪) := by
    have e : u - 1 = -(u * sgA D (u - 1)) := by
      rw [map_sub, map_one, mul_sub, hn]; ring
    rw [e]
    exact neg_mem (mul_mem_hatId huO (sgA_mem_hatId h1))
  have hsup : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ := by
    rw [← Ideal.add_eq_sup, Ideal.isCoprime_iff_add.1 hco, Ideal.one_eq_top]
  have h1m : (1 : 𝓞 D.host.E) ∈ 𝔪 ⊔ D.host.conj • 𝔪 := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 h1m
  have e : u - 1 = inc D (s : D.host.E) * (u - 1) + inc D (t : D.host.E) * (u - 1) := by
    rw [← add_mul, ← map_add (f := _), show (s : D.host.E) + t = ((s + t : 𝓞 D.host.E) : D.host.E) from rfl, hst]; simp
  rw [e]
  refine add_mem (inc_mul_mem_hatId hs h2) ?_
  rw [mul_comm 𝔪]
  exact inc_mul_mem_hatId ht h1

end GlobalTheory.FunObj.StdDatum.DetCong

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VlLeOfMemHatId
section
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

noncomputable section

namespace GlobalTheory.NuTrivSq
variable {D : D7}

open GlobalTheory.Mem.Col2.SplitChar in
theorem vl_le_of_mem_hatId' {I : Ideal (𝓞 D.host.E)} {PP : HeightOneSpectrum (𝓞 D.host.E)} {n : ℕ}
    (hI : I ≤ PP.asIdeal ^ n) {x : AE D} (hx : x ∈ hatId D I) : vl D PP x ≤ WithZero.exp (-(n : ℤ)) := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    rw [map_mul, vl_inc]
    refine (mul_le_of_le_one_right' (vl_le hs PP)).trans ?_
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_le_pow_iff_mem PP b n).2 (hI hb)
  | zero => simp
  | add a b _ _ ha hb => exact (Valuation.map_add _ _ _).trans (max_le ha hb)
  | neg a _ ha => rwa [Valuation.map_neg]


open GlobalTheory.Mem.Col2.SplitChar in
theorem sgA_mem_hatId' {I : Ideal (𝓞 D.host.E)} {x : AE D} (hx : x ∈ hatId D I) :
    sgA D x ∈ hatId D (D.host.conj • I) := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨D.host.conj • b, Ideal.smul_mem_pointwise_smul _ _ _ hb, sgA D s,
      GlobalTheory.NormSum.UnramHecke.sgA_mem D hs, ?_⟩
    rw [map_mul, GlobalTheory.Mem.Col2.SplitChar.sgA_inc]
    rfl
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

theorem conj_conj_smul (𝔪 : Ideal (𝓞 D.host.E)) : D.host.conj • D.host.conj • 𝔪 = 𝔪 := by
  have h : D.host.conj * D.host.conj = 1 := AlgEquiv.ext fun z => GlobalTheory.NormSum.UnramHecke.conj_conj D z
  rw [smul_smul, h, one_smul]


open GlobalTheory.Mem.Col2.SplitChar in
theorem vl_sub_le' {T : Type} {L : LevCh D T} (P : Places L) {y : AE D}
    (h1 : y ∈ hatId D (condE P)) (h2 : y ∈ hatId D (D.host.conj • condE P))
    {PP : HeightOneSpectrum (𝓞 D.host.E)} (hv : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ P.S0) :
    vl D PP y ≤ WithZero.exp (-(condExp P ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) : ℤ)) := by
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  set v := (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) with hvdef
  have hw : (P.w v).under (𝓞 D.host.F) = v := P.under_w hv
  have hle : condE P ≤ (P.w v).asIdeal ^ condExp P v := Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hv)
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl c hcm.rank hcm.ne (P.w v) PP).1 (by rw [hw]) with e | h
  · rw [e]
    exact vl_le_of_mem_hatId' (e ▸ hle) h1
  · have e : c.toRingEquiv = D.host.conj.toRingEquiv := RingEquiv.ext hc
    rw [e] at h
    rw [← GlobalTheory.NormSum.UnramHecke.sgA_sgA D y, vl_sgA h]
    have h3 := sgA_mem_hatId' h2
    rw [conj_conj_smul] at h3
    exact vl_le_of_mem_hatId' hle h3

end GlobalTheory.NuTrivSq


open GlobalTheory.Mem.Col2.SplitChar Formalism.L2.Host GlobalTheory.NuTrivSq in
theorem GlobalTheory.NuTrivSq.nuH_finIdl_eq_one : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i j : Fin D.R.m) {μ₀ : T},
    L.Is μ₀ → ∀ x : (AE D)ˣ, IntU D x → (x : AE D) - 1 ∈ hatId D (condE G.pl) →
      (x : AE D) - 1 ∈ hatId D (D.host.conj • condE G.pl) →
      (nuH G μ₀ i j).1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D x) = 1 := by
  intro D T L sc G i j μ₀ hL u hu hc1 hc2
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local D.host.E _ (nuH G μ₀ i j).2.1 (finIdl D u) (finIdl_unit hu)
    (fun w => by rw [finIdl_fst]; rfl) fun PP x hx => ?_
  have hunit : IsUnitAt PP x := by
    unfold IsUnitAt
    rw [hx]
    exact finIdl_unit hu PP
  have hsub : Valued.v ((x : PP.adicCompletion D.host.E) - 1) = vl D PP ((u : AE D) - 1) := by
    rw [hx, vl_sub_one]
  have hμ : (L.C.mu0 j).loc PP x = 1 := by
    by_cases hg : ∃ k, OverP D.host (D.host.g k) PP
    · obtain ⟨k, hk⟩ := hg
      have hS : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ G.pl.S0 := by
        refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_))
        have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal := by
          change _ ∈ PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
          rw [Ideal.mem_comap, map_natCast]
          exact hk
        fin_cases k
        · exact Or.inl this
        · exact Or.inr (Or.inl this)
      refine (L.C.isMu0 j).tame PP x hunit ?_
      rw [hsub]
      refine (vl_sub_le' G.pl hc1 hc2 hS).trans ?_
      have : 1 ≤ condExp G.pl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by unfold condExp; split_ifs <;> omega
      exact WithZero.exp_le_exp.2 (by omega)
    · push_neg at hg
      exact (L.C.isMu0 j).unr PP hg x hunit
  have hχ : (G.ch.chiH (D.R.m - i)).loc PP x = 1 := by
    have h1 : 1 ≤ D.R.m - (i : ℕ) := by omega
    have h2 : D.R.m - (i : ℕ) ≤ D.R.m := by omega
    by_cases hS : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ G.pl.S0
    · have hb := vl_sub_le' G.pl hc1 hc2 hS
      rw [← hsub] at hb
      rcases G.pl.mem_S0_of_sum_eq.1 hS with h0 | h1'
      · rw [condExp, if_pos h0] at hb
        exact (G.ch.lev0 _ h1 h2 PP h0).1 x hunit (by simpa using hb)
      · have hne : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ G.pl.v0 := fun e => G.ch.basePlace_not_mem_chiGridBadPlaces (e ▸ h1')
        rw [condExp, if_neg hne] at hb
        exact (G.ch.lev1 _ h1 h2 PP h1').1 x hunit (by simpa using hb)
    · exact G.ch.unr _ h1 h2 PP hS x hunit
  show (nuH G μ₀ i j).loc PP x = 1
  rw [nuH, hL.xi_base, mul_one, div_eq_mul_inv]
  change (L.C.mu0 j).loc PP x * ((G.ch.chiH (D.R.m - i)).loc PP x)⁻¹ = 1
  rw [hμ, hχ, inv_one, one_mul]

end
end

