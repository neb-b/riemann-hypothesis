module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1343

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PKapOf
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open GlobalTheory.LFun (KGL)
open scoped Classical

private theorem scal_mem_KGL {E : Type} [Field E] [NumberField E] {n : ℕ} {u : Plc E}
    (a b : GL (Fin n) (u.adicCompletion E)) (t q : u.adicCompletion E)
    (ha : a.val = t • (1 : Matrix (Fin n) (Fin n) _)) (hb : b.val = q • (1 : Matrix (Fin n) (Fin n) _))
    (hq : q ≠ 0) (hv : Valued.v t = Valued.v q) : a⁻¹ * b ∈ KGL u (n := n) := by
  have hq' : Valued.v q ≠ 0 := (Valuation.ne_zero_iff _).2 hq
  have ht : t ≠ 0 := by
    rintro rfl
    exact hq' (by rw [← hv, map_zero])
  have hai : (a⁻¹).val = t⁻¹ • (1 : Matrix (Fin n) (Fin n) _) :=
    Units.inv_eq_of_mul_eq_one_right (by rw [ha]; simp [smul_smul, ht])
  have hbi : (b⁻¹).val = q⁻¹ • (1 : Matrix (Fin n) (Fin n) _) :=
    Units.inv_eq_of_mul_eq_one_right (by rw [hb]; simp [smul_smul, hq])
  have e1 : (a⁻¹ * b).val = (t⁻¹ * q) • (1 : Matrix (Fin n) (Fin n) _) := by
    rw [Units.val_mul, hai, hb]; simp [smul_smul, mul_comm]
  have e2 : ((a⁻¹ * b)⁻¹).val = (q⁻¹ * t) • (1 : Matrix (Fin n) (Fin n) _) := by
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, hbi, ha]; simp [smul_smul, mul_comm]
  have v1 : Valued.v (t⁻¹ * q) = 1 := by
    rw [map_mul, map_inv₀, hv, inv_mul_cancel₀ hq']
  have v2 : Valued.v (q⁻¹ * t) = 1 := by
    rw [map_mul, map_inv₀, hv, inv_mul_cancel₀ hq']
  have key : ∀ (c : u.adicCompletion E), Valued.v c = 1 → ∀ i j,
      Valued.v ((c • (1 : Matrix (Fin n) (Fin n) (u.adicCompletion E))) i j) ≤ 1 := by
    intro c hc i j
    rw [Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp [hc]
  refine (GlobalTheory.BCT.GlobLev.mem_KGL_iff_val u _).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [e1]; exact key _ v1 i j
  · rw [e2]; exact key _ v2 i j

theorem UpperTheory.Gal.CertificateRingHomMap.pKapOf_of :
    UpperTheory.Gal.CertificateRingHomMap.FinToHecke → UpperTheory.Gal.CertificateRingHomMap.XiZeta → UpperTheory.Gal.CertificateRingHomMap.IntSim → UpperTheory.Gal.CertificateRingHomMap.LevOpen → UpperTheory.Gal.CertificateRingHomMap.KapOf := by
  intro hFH hXi hIS hLO E _ _ _ n hn x ζ hζ U W j Up w₀ S Kw hS χ hχ Φ ψ hΦ hψ
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, Φ g₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hΦ.ne (funext h)
  have cancel : ∀ a b : ℂ, a • Φ g₀ = b • Φ g₀ → a = b := fun a b h => smul_left_injective ℂ hg₀ h
  have A : ∀ k ∈ lev S Kw, ∀ h : comp w₀ k ∈ Kw w₀, χ ⟨comp w₀ k, h⟩ = 1 → ∀ g, Φ (g * k) = Φ g := by
    intro k hk h h1 g
    rw [hΦ.right k hk h g, h1]
    simp
  have B : ∀ y, (∀ g, Φ (g * ζ y) = Φ g) → ψ y = 1 := by
    intro y hy
    have h := hy g₀
    rw [hψ] at h
    exact Units.ext (cancel _ 1 (by simpa using h))
  have C : ∀ k : GUf E n, (∀ u, comp u k ∈ KGL u (n := n)) → (∀ u ∈ S, comp u k = 1) → k ∈ lev S Kw :=
    fun k h1 h2 => mem_lev.2 ⟨hIS E n hn k h1, fun u hu => by rw [h2 u hu]; exact one_mem _, fun u _ _ => h1 u⟩
  have D : ∀ k ∈ lev S Kw, comp w₀ k = 1 → ∀ g, Φ (g * k) = Φ g := by
    intro k hk h1 g
    have h : comp w₀ k ∈ Kw w₀ := by rw [h1]; exact one_mem _
    refine A k hk h ?_ g
    have e : (⟨comp w₀ k, h⟩ : Kw w₀) = 1 := Subtype.ext h1
    rw [e, map_one]

  have hKo : IsOpen ((χ.ker.map (Kw w₀).subtype : Subgroup (GLw n w₀)) : Set (GLw n w₀)) := by
    have e : ((χ.ker.map (Kw w₀).subtype : Subgroup (GLw n w₀)) : Set (GLw n w₀)) =
        Subtype.val '' {k : Kw w₀ | χ k = 1} := by
      ext a
      simp [Subgroup.mem_map, MonoidHom.mem_ker]
    rw [e]
    exact (hS.opn w₀ hS.mem).isOpenMap_subtype_val _ hχ
  have hK' := hLO E n S (Function.update Kw w₀ (χ.ker.map (Kw w₀).subtype)) (by
    intro w hw
    by_cases h : w = w₀
    · subst h
      simpa using hKo
    · simpa [Function.update_of_ne h] using hS.opn w hw)
  have hker : IsOpen (((ψ⁻¹).ker : Subgroup (Af E)ˣ) : Set (Af E)ˣ) := by
    refine Subgroup.isOpen_mono (H₁ := (lev S (Function.update Kw w₀ (χ.ker.map (Kw w₀).subtype))).comap ζ) ?_
      (hK'.preimage hζ.cont)
    intro y hy
    have hy' := mem_lev.1 (Subgroup.mem_comap.1 hy)
    have h0 := hy'.2.1 w₀ hS.mem
    rw [Function.update_self] at h0
    obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.1 h0
    have hl : ζ y ∈ lev S Kw := by
      refine mem_lev.2 ⟨hy'.1, fun u hu => ?_, hy'.2.2⟩
      by_cases h : u = w₀
      · subst h
        rw [← hae]
        exact a.2
      · have := hy'.2.1 u hu
        rwa [Function.update_of_ne h] at this
    have h1 : ψ y = 1 := by
      refine B y fun g => A _ hl (by rw [← hae]; exact a.2) ?_ g
      have e : (⟨comp w₀ (ζ y), by rw [← hae]; exact a.2⟩ : Kw w₀) = a := Subtype.ext hae.symm
      rw [e]
      exact ha
    rw [MonoidHom.mem_ker, MonoidHom.inv_apply, h1, inv_one]
  have hprin : ∀ k : Eˣ, (((ψ⁻¹) (diagF E k) : ℂˣ) : ℂ) = (∏ φ : E →+* ℂ, φ (k : E) ^ mOf x W j φ)⁻¹ := by
    intro k
    obtain ⟨γ, h1, h2⟩ := hXi E n W j x ζ hζ k
    have e : ((ψ (diagF E k) : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, φ (k : E) ^ mOf x W j φ := by
      apply cancel
      rw [← hψ, ← hζ.central, h1, hΦ.left, h2]
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, e]
  obtain ⟨κ, halg, hloc⟩ := hFH E (ψ⁻¹) (mOf x W j) hker hprin
  refine ⟨κ, halg, ?_, ?_⟩
  · intro w hw y hy
    have h1 : ψ (sgl w y) = 1 := by
      refine B _ fun g => D _ (C _ (hζ.unit w y hy) fun u hu => hζ.off w y u (hw u hu)) ?_ g
      exact hζ.off w y w₀ (hw w₀ hS.mem)
    rw [hloc, MonoidHom.inv_apply, h1, inv_one]
  · intro w hw hnw z hz g
    have hv : κ.val w = (ψ (sgl w (atFin w (unif w))))⁻¹ := by
      show κ.loc w (atFin w (unif w)) = _
      rw [hloc, MonoidHom.inv_apply]
    have hq : ∀ u : Plc E, ((Ideal.absNorm w.asIdeal : ℕ) : u.adicCompletion E) ≠ 0 := by
      intro u
      have h0 : Ideal.absNorm w.asIdeal ≠ 0 := by
        simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot
      exact Nat.cast_ne_zero.2 h0
    have hc : ∀ u, comp u ((ζ (sgl w (atFin w (unif w))))⁻¹ * z) ∈ KGL u (n := n) ∧
        (¬ SameK x (cj u) w → comp u ((ζ (sgl w (atFin w (unif w))))⁻¹ * z) = 1) := by
      intro u
      have hoff : ¬ SameK x (cj u) w → comp u ((ζ (sgl w (atFin w (unif w))))⁻¹ * z) = 1 := by
        intro h
        rw [map_mul, map_inv, hζ.off w _ u h, (hz u).2 h, inv_one, one_mul]
      refine ⟨?_, hoff⟩
      by_cases h : SameK x (cj u) w
      · obtain ⟨t, ht, hvt⟩ := hζ.unif w _ (unif_spec w) hnw u h
        rw [map_mul, map_inv]
        exact scal_mem_KGL _ _ t _ ht ((hz u).1 h) (hq u) hvt
      · rw [hoff h]
        exact one_mem _
    have hk : (ζ (sgl w (atFin w (unif w))))⁻¹ * z ∈ lev S Kw :=
      C _ (fun u => (hc u).1) fun u hu => (hc u).2 (hw u hu)
    have e : z = ζ (sgl w (atFin w (unif w))) * ((ζ (sgl w (atFin w (unif w))))⁻¹ * z) := by
      rw [mul_inv_cancel_left]
    rw [e, ← mul_assoc, D _ hk ((hc w₀).2 (hw w₀ hS.mem)), hψ, hv]
    simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PKerFormU
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap

private theorem rat_eq_one_of_ZU (s : ℚˣ) (hpos : 0 < (s : ℚ))
    (h : Units.map (algebraMap ℚ AfQ).toMonoidHom s ∈ ZU) : s = 1 := by
  have hv : ∀ v : Plc ℚ, HeightOneSpectrum.valuation ℚ v (s : ℚ) = 1 := fun v => by
    have h1 : Valued.v ((algebraMap ℚ AfQ (s : ℚ)) v) = 1 := h v
    rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
    exact h1
  have hi : ∀ x : ℚ, (∀ v : Plc ℚ, HeightOneSpectrum.valuation ℚ v x ≤ 1) → ∃ m : ℤ, (m : ℚ) = x := fun x hx => by
    obtain ⟨a, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ x hx
    have h2 : IsIntegral ℤ (algebraMap (𝓞 ℚ) ℚ a) := a.2
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
    exact ⟨m, by simpa using hm⟩
  obtain ⟨m, hm⟩ := hi s (fun v => (hv v).le)
  obtain ⟨m', hm'⟩ := hi (s : ℚ)⁻¹ (fun v => by rw [map_inv₀, hv v, inv_one])
  have hmm : m * m' = 1 := by
    have h3 : (m : ℚ) * m' = 1 := by rw [hm, hm']; exact mul_inv_cancel₀ s.ne_zero
    exact_mod_cast h3
  have hm1 : m = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hmm with h4 | h4
    · exact h4
    · subst h4
      rw [← hm] at hpos
      norm_num at hpos
  ext
  rw [← hm, hm1]
  simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem coord_emb (v : InfinitePlace E) (x : E) :
    coord v.embedding (pInf E (algebraMap E (Ad E) x)) = v.embedding x := by
  have h : ∀ w : InfinitePlace E, pInf E (algebraMap E (Ad E) x) w = w.embedding x := fun w => pInf_algebraMap _ _
  unfold coord
  simp [h]

private theorem val_rat (W : Wt E n) (j : ℤ) (f : algForms W) (γ : Gam0 E n) (h1 : γ.1.2 = 1) :
    ∃ a : finU (E := E) (n := n), ofU a = rat γ ∧
      ∀ u : finU (E := E) (n := n), algForms.val f (a.1 * u.1) = xi0 W j γ (algForms.val f u.1) := by
  have hy : (γ.1.1.val.map (GlobalTheory.SplitPts.conjE E).toRingHom)ᵀ * γ.1.1.val = 1 := by
    have h : (γ.1.1.val.map (GlobalTheory.SplitPts.conjE E).toRingHom)ᵀ * γ.1.1.val =
      algebraMap ℚ E γ.1.2 • (1 : Matrix (Fin n) (Fin n) E) := γ.2.1
    rw [h, h1]
    simp
  have hY : ratGL E n γ.1.1 ∈ UA E n := by
    change Formalism.UG.cT (conjAd E) (γ.1.1.val.map (algebraMap E (Ad E))) * 1 * γ.1.1.val.map (algebraMap E (Ad E)) = 1
    rw [GlobalTheory.DefU.ClassFin.cT_map (algebraMap E (Ad E)) (IsCMField.complexConj E).toRingEquiv.toRingHom (conjAd E)
      (fun y => (conjAd_algebraMap y).symm), mul_one, ← Matrix.map_mul]
    have h2 : Formalism.UG.cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.1.val * γ.1.1.val = 1 := hy
    rw [h2]
    simp
  let Y : UA E n := ⟨ratGL E n γ.1.1, hY⟩
  have hYr : Y ∈ ratU E n := Subgroup.mem_subgroupOf.2 ⟨γ.1.1, rfl⟩
  let a := GlobalTheory.UnitarySplit.finPart Y
  let b := GlobalTheory.UnitarySplit.infPart Y
  have hab : Y = a.1 * b.1 := GlobalTheory.UnitarySplit.finPart_mul_infPart Y
  refine ⟨a, ?_, fun u => ?_⟩
  · refine Subtype.ext (Prod.ext ?_ ?_)
    · exact pFin_finGL _
    · show (1 : AfQˣ) = Units.map (algebraMap ℚ AfQ).toMonoidHom γ.1.2
      rw [h1, map_one]
  · have e : a.1 * u.1 = Y * (u.1 * ((b⁻¹ : infU E n) : UA E n)) := by
      have hc := GlobalTheory.DefU.fin_mul_inf u.2 b.2
      rw [hab, Subgroup.coe_inv, mul_assoc, ← mul_assoc b.1, ← hc, mul_assoc u.1, mul_inv_cancel, mul_one]
    have hc : cAll b.1 = embAll E n γ.1.1 := by
      funext v
      show cEmb v.embedding b.1 = GeneralLinearGroup.map v.embedding γ.1.1
      refine Units.ext (Matrix.ext fun i k => ?_)
      have h3 : (cEmb v.embedding b.1).val i k = coord v.embedding ((cInf b.1).val i k) := rfl
      rw [h3, GlobalTheory.UnitarySplit.cInf_infPart]
      exact coord_emb v _
    rw [e, algForms.val_left f hYr, algForms.val_right, inv_inv]
    have h4 : xi0 W j γ = Representation.dual
        ((Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W).comp (embAll E n)) γ.1.1 := by
      have h6 : xi0 W j γ = (((γ.1.2 : ℚ) : ℂ) ^ j) • Representation.dual
          ((Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W).comp (embAll E n)) γ.1.1 := rfl
      rw [h6, h1]
      simp
    rw [h4, Representation.dual_apply, Representation.dual_apply]
    have h5 : W.rep b⁻¹ = ((Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W).comp (embAll E n)) γ.1.1⁻¹ := by
      have h7 : cAll (b⁻¹ : infU E n).1 = embAll E n γ.1.1⁻¹ := by
        rw [Subgroup.coe_inv, map_inv, hc, map_inv]
      show Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W (cAll (b⁻¹ : infU E n).1) =
        Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W (embAll E n γ.1.1⁻¹)
      rw [h7]
    rw [h5]

theorem pKerFormU_of :
    UpperTheory.Gal.CertificateRingHomMap.OfUBij → UpperTheory.Gal.CertificateRingHomMap.KerFormU := by
  intro hB E _ _ _ n W j f hf K hK hfix
  obtain ⟨hinj, hsurj⟩ := hB E n
  let φ : GUf E n → Module.Dual ℂ W.Sp := fun g => if h : ∃ u, ofU u = g then algForms.val f h.choose.1 else 0
  have hφ : ∀ u : finU (E := E) (n := n), φ (ofU u) = algForms.val f u.1 := fun u => by
    have h : ∃ u', ofU u' = ofU u := ⟨u, rfl⟩
    show (if h : ∃ u', ofU u' = ofU u then algForms.val f h.choose.1 else 0) = _
    rw [dite_eq_left h, hinj h.choose_spec]
  have hone : ∀ γ : Gam0 E n, sim (rat γ) ∈ ZU → γ.1.2 = 1 := fun γ h => rat_eq_one_of_ZU γ.1.2 γ.2.2 h
  refine ⟨φ, ⟨?_, ?_, ?_⟩, hφ, ?_⟩
  · intro γ k hk he
    have h1 := hone γ (he ▸ hK k hk)
    rw [← he]
    show Units.map (algebraMap ℚ AfQ).toMonoidHom γ.1.2 = 1
    rw [h1, map_one]
  · intro γ u hγ hu
    obtain ⟨u₀, rfl⟩ := hsurj u hu
    obtain ⟨a, ha, hau⟩ := val_rat W j f γ (hone γ (hγ ▸ ZU.one_mem))
    rw [← ha, ← map_mul, hφ, hφ]
    exact hau u₀
  · intro k hk u hk1 hu
    obtain ⟨u₀, rfl⟩ := hsurj u hu
    obtain ⟨u', rfl⟩ := hsurj k hk1
    rw [← map_mul, hφ, hφ]
    show algForms.val f (u₀.1 * u'.1) = _
    rw [← algForms.val_algRep, hfix u' hk]
  · have hex : ∃ g, algForms.val f g ≠ 0 := by
      by_contra hc
      push_neg at hc
      refine hf (Subtype.ext (LinearMap.ext fun v => funext fun g => ?_))
      exact LinearMap.congr_fun (hc g) v
    obtain ⟨g, hg⟩ := hex
    refine ⟨ofU (GlobalTheory.UnitarySplit.finPart g), sim_ofU _, ?_⟩
    rw [hφ]
    intro h0
    apply hg
    have h1 := algForms.val_right f (GlobalTheory.UnitarySplit.finPart g).1 (GlobalTheory.UnitarySplit.infPart g)
    rw [← GlobalTheory.UnitarySplit.finPart_mul_infPart g] at h1
    rw [h1, h0, map_zero]

end UpperTheory.Gal.CertificateRingHomMap
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PLevOpen
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

private theorem isOpen_intA (F : Type) [Field F] [NumberField F] :
    IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, Valued.v (a v) ≤ 1} :=
  RestrictedProduct.isOpen_forall_mem
    (A := fun v : HeightOneSpectrum (𝓞 F) => ((v.adicCompletionIntegers F : ValuationSubring _) : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _)

private theorem continuous_sim {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} :
    Continuous (sim : GUf E n → AfQˣ) := continuous_snd.comp continuous_subtype_val

private theorem continuous_mat {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} :
    Continuous (mat : GUf E n → GL (Fin n) (Af E)) := continuous_fst.comp continuous_subtype_val

private theorem continuous_comp {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (w : Plc E) :
    Continuous (comp w : GUf E n → GL (Fin n) (w.adicCompletion E)) :=
  (Continuous.units_map _ (continuous_id.matrix_map (RestrictedProduct.continuous_eval w))).comp continuous_mat

theorem UpperTheory.Gal.CertificateRingHomMap.pLevOpen_of :
    UpperTheory.Gal.CertificateRingHomMap.LevOpen := by
  intro E _ _ _ n S Kw hK
  have hI : IsOpen {a : Af E | ∀ v, Valued.v (a v) ≤ 1} := isOpen_intA E
  have hJ : IsOpen {a : AfQ | ∀ v, Valued.v (a v) ≤ 1} := isOpen_intA ℚ
  let A : Set (GUf E n) :=
    ((((fun k => ((sim k : AfQˣ) : AfQ)) ⁻¹' {a : AfQ | ∀ v, Valued.v (a v) ≤ 1}) ∩
      ((fun k => (((sim k)⁻¹ : AfQˣ) : AfQ)) ⁻¹' {a : AfQ | ∀ v, Valued.v (a v) ≤ 1})) ∩
    ((⋂ i, ⋂ j, (fun k => (mat k).val i j) ⁻¹' {a : Af E | ∀ v, Valued.v (a v) ≤ 1}) ∩
      (⋂ i, ⋂ j, (fun k => ((mat k)⁻¹).val i j) ⁻¹' {a : Af E | ∀ v, Valued.v (a v) ≤ 1}))) ∩
    ⋂ w ∈ S, comp w ⁻¹' (Kw w : Set (GLw n w))
  have hAo : IsOpen A := by
    refine ((IsOpen.inter ?_ ?_).inter (IsOpen.inter ?_ ?_)).inter ?_
    · exact hJ.preimage (Units.continuous_val.comp continuous_sim)
    · exact hJ.preimage (Units.continuous_val.comp continuous_sim.inv)
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        hI.preimage ((Units.continuous_val.comp continuous_mat).matrix_elem i j)
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        hI.preimage ((Units.continuous_val.comp continuous_mat.inv).matrix_elem i j)
    · exact isOpen_biInter_finset fun w hw => (hK w hw).preimage (continuous_comp w)
  have hone : ∀ (i j : Fin n) (v : Plc E), Valued.v (((1 : Matrix (Fin n) (Fin n) (Af E)) i j) v) ≤ 1 := by
    intro i j v
    by_cases h : i = j
    · subst h
      rw [Matrix.one_apply_eq]
      change Valued.v (1 : v.adicCompletion E) ≤ 1
      rw [map_one]
    · rw [Matrix.one_apply_ne h]
      change Valued.v (0 : v.adicCompletion E) ≤ 1
      rw [map_zero]
      exact zero_le'
  have hQ : ∀ v : Plc ℚ, Valued.v ((1 : AfQ) v) ≤ 1 := fun v => by
    change Valued.v (1 : v.adicCompletion ℚ) ≤ 1
    rw [map_one]
  have h1 : (1 : GUf E n) ∈ A := by
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · simpa using hQ
    · simpa using hQ
    · simp only [Set.mem_iInter, Set.mem_preimage, map_one]
      exact fun i j => hone i j
    · simp only [Set.mem_iInter, Set.mem_preimage, map_one, inv_one]
      exact fun i j => hone i j
    · simp only [Set.mem_iInter, Set.mem_preimage, map_one]
      exact fun w _ => (Kw w).one_mem
  have hsub : A ⊆ (lev S Kw : Set (GUf E n)) := by
    rintro k ⟨⟨⟨hs, hs'⟩, hm, hm'⟩, hc⟩
    simp only [Set.mem_iInter, Set.mem_preimage] at hm hm' hc
    refine mem_lev.2 ⟨fun v => ?_, fun w hw => hc w hw, fun w _ _ => ?_⟩
    · have h : Valued.v (((sim k : AfQˣ) : AfQ) v * (((sim k)⁻¹ : AfQˣ) : AfQ) v) = 1 := by
        change Valued.v ((((sim k : AfQˣ) : AfQ) * (((sim k)⁻¹ : AfQˣ) : AfQ)) v) = 1
        rw [Units.mul_inv]
        exact map_one _
      rw [map_mul] at h
      refine le_antisymm (hs v) ?_
      calc (1 : _) = _ := h.symm
        _ ≤ Valued.v (((sim k : AfQˣ) : AfQ) v) * 1 := mul_le_mul' le_rfl (hs' v)
        _ = _ := mul_one _
    · rw [GlobalTheory.HenQ.Basic.mem_KGL_iff]
      refine ⟨fun i j => hm i j w, fun i j => ?_⟩
      have : (comp w k)⁻¹ = GeneralLinearGroup.map (pLoc E w) (mat k)⁻¹ := (map_inv _ _).symm
      rw [this]
      exact hm' i j w
  exact Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (hAo.mem_nhds h1) hsub)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PLocComm
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap.LocalCommutativity

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem rel (k : GUf E n) (u : Plc E) :
    ((comp (cj u) k).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) u))ᵀ * (comp u k).val =
      pLoc E u (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim k : AfQˣ) : AfQ)) •
        (1 : Matrix (Fin n) (Fin n) (u.adicCompletion E)) := by
  have h := mem_Sim.1 k.2
  have h2 := congrArg (RingHom.mapMatrix (pLoc E u)) h
  rw [map_mul] at h2
  refine h2.trans ?_
  ext i j
  by_cases hij : i = j <;> simp [hij, Matrix.one_apply, sim]

private theorem gu_ext {a b : GUf E n} (hs : sim a = sim b) (hc : ∀ u, comp u a = comp u b) : a = b := by
  refine Subtype.ext (Prod.ext (Units.ext (GlobalTheory.SplitPts.matAf_ext fun u => ?_)) hs)
  exact congrArg Units.val (hc u)

private theorem comm_scalar {R : Type} [CommRing R] (M X : Matrix (Fin n) (Fin n) R)
    (ho : ∀ i j, i ≠ j → M i j = 0) (hd : ∀ i j, M i i = M j j) : M * X = X * M := by
  have e : M = Matrix.diagonal (fun i => M i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, ho i j hij]
  ext i j
  rw [e, Matrix.diagonal_mul, Matrix.mul_diagonal, hd i j, mul_comm]

end UpperTheory.Gal.CertificateRingHomMap.LocalCommutativity

open UpperTheory.Gal.CertificateRingHomMap.LocalCommutativity in
theorem UpperTheory.Gal.CertificateRingHomMap.pLocComm_of :
    UpperTheory.Gal.CertificateRingHomMap.LocComm := by
  intro E _ _ _ n w hw
  obtain ⟨hne, hund, hover⟩ := GlobalTheory.SplitPts.over_split hw
  have hcc : cj (cj w) = w := GlobalTheory.SplitPts.conjSrc_conjSrc_cm w
  have hap : ∀ u, GlobalTheory.Cong.Apart u w ↔ u ≠ w ∧ u ≠ cj w := by
    intro u
    constructor
    · intro h
      exact ⟨fun e => h (by rw [e]), fun e => h (by rw [e]; exact hund)⟩
    · rintro ⟨h1, h2⟩ h
      rcases hover u h with e | e
      · exact h1 e
      · exact h2 e
  refine ⟨?_, hap, hne, ⟨w, hne.symm, hund.symm⟩, hcc, ?_⟩
  · intro k hk y
    refine gu_ext (by rw [map_mul, map_mul]; exact mul_comm _ _) fun u => ?_
    rw [map_mul, map_mul]
    by_cases h1 : u = w
    · subst h1
      rw [hk, one_mul, mul_one]
    by_cases h2 : u = cj w
    · subst h2
      have r := rel k w
      rw [hk, Units.val_one, Matrix.mul_one] at r
      have r' := congrArg Matrix.transpose r
      rw [Matrix.transpose_transpose, Matrix.transpose_smul, Matrix.transpose_one] at r'
      have hent : ∀ i j, conjLoc (GlobalTheory.SplitPts.conjE E) w ((comp (cj w) k).val i j) = _ :=
        fun i j => congrFun (congrFun r' i) j
      have hinj := (conjLoc (GlobalTheory.SplitPts.conjE E) w).injective
      refine Units.ext ?_
      rw [Units.val_mul, Units.val_mul]
      refine comm_scalar _ _ (fun i j hij => hinj ?_) (fun i j => hinj ?_)
      · rw [hent i j, map_zero]; simp [hij]
      · rw [hent i i, hent j j]; simp
    · rw [comp_loc_of_apart hw ((hap u).2 ⟨h1, h2⟩), mul_one, one_mul]
  · unfold locU
    rw [hund]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PLocMem
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pLocMem_of :
    UpperTheory.Gal.CertificateRingHomMap.IntConj → UpperTheory.Gal.CertificateRingHomMap.LocComm → UpperTheory.Gal.CertificateRingHomMap.LocMem := by
  intro hIC hLC E _ _ _ n S Kw w hw hcw y
  obtain ⟨-, hap, -, -, hcc, -⟩ := hLC E n w hw
  have hsim : sim (loc hw y) ∈ ZU := by
    rw [sim_loc]; exact ZU.one_mem
  have hone : ∀ u, u ≠ w → u ≠ cj w → comp u (loc hw y) = 1 := fun u h1 h2 =>
    comp_loc_of_apart hw ((hap u).2 ⟨h1, h2⟩) y
  refine ⟨fun hwS hy => mem_lev.2 ⟨hsim, ?_, ?_⟩, fun hwS hy => mem_lev.2 ⟨hsim, ?_, ?_⟩⟩
  · intro u hu
    by_cases h1 : u = w
    · subst h1
      rw [comp_loc]; exact hy
    · have h2 : u ≠ cj w := fun h => hcw (h ▸ hu)
      rw [hone u h1 h2]; exact (Kw u).one_mem
  · intro u hu hcu
    have h1 : u ≠ w := fun h => hu (h ▸ hwS)
    have h2 : u ≠ cj w := fun h => hcu (by rw [h, hcc]; exact hwS)
    rw [hone u h1 h2]; exact (GlobalTheory.LFun.KGL u (n := n)).one_mem
  · intro u hu
    have h1 : u ≠ w := fun h => hwS (h ▸ hu)
    have h2 : u ≠ cj w := fun h => hcw (h ▸ hu)
    rw [hone u h1 h2]; exact (Kw u).one_mem
  · intro u hu hcu
    by_cases h1 : u = w
    · subst h1
      rw [comp_loc]; exact hy
    · by_cases h2 : u = cj w
      · subst h2
        exact hIC E n (loc hw y) w hsim (by rw [comp_loc]; exact hy)
      · rw [hone u h1 h2]; exact (GlobalTheory.LFun.KGL u (n := n)).one_mem
end

