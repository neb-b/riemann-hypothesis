module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.Bundle0018
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.Bundle0019
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ValuationDetCongruenceSubgroupEqOne

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.HyperbolicTermsIntegrableProof
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc

namespace UpperTheory.Esk.HyperbolicIntegrabilityLemmas

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem pInf_alg (v : InfinitePlace F) (x : F) :
    TR.pInf F (algebraMap F (Ad F) x) v = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x := by
  have e : TR.pInf F (algebraMap F (Ad F) x) v = (v.embedding x).re := by
    rw [← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v), Complex.ofReal_re]
    change InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v) (algebraMap F (InfiniteAdeleRing F) x v) = _
    simp
  rw [e, ← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v), Complex.ofReal_re]

omit [IsTotallyReal F] in
theorem fin_zc (u : (Af F)ˣ) : finGL F 2 (zc F u) = Matrix.GeneralLinearGroup.scalar (Fin 2) (finId F u) := by
  rw [zc, finGL, GlobalTheory.CuspRep.cornerGL_scalar]
  rfl

def rr (γ : GL (Fin 2) F) : GL (Fin 2) (TR.Rinf F) := Matrix.GeneralLinearGroup.map ((TR.pInf F).comp (algebraMap F (Ad F))) γ

theorem gv_rr (c : Pl F → ℕ) (χ : Hc c →* ℂˣ) (γ : GL (Fin 2) F) (v : InfinitePlace F) : gv v (rr γ) = (mkDat c χ).r v γ :=
  Units.ext (Matrix.ext fun i j => pInf_alg v (γ i j))

theorem rat_eq (γ : GL (Fin 2) F) : ratGL F 2 γ = TR.infGL F 2 (rr γ) * finGL F 2 (jF F γ) := by
  rw [← TR.infGL_mul_finGL (ratGL F 2 γ)]
  rfl

omit [IsTotallyReal F] in
theorem sc_comm (s : Ideles F) (a : GA F 2) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) s * a = a * Matrix.GeneralLinearGroup.scalar (Fin 2) s :=
  Units.ext (Matrix.scalar_commute (s : Ad F) (fun _ => Commute.all _ _) a.val).eq

theorem aut (hb : B1b) (k : InfinitePlace F → ℕ) (c : Pl F → ℕ) (χ : Hc c →* ℂˣ) (φ : TR.Sm F 2) (hφ : TR.IsAutForm φ)
    (f : X (InfinitePlace F) × GF F → ℂ) (hf : Rel k f φ.1) (γ : GL (Fin 2) F) (g : GL (Fin 2) (TR.Rinf F)) (x : GF F) :
    f ((mkDat c χ).act γ (fun v => gv v g • iP), jF F γ * x) =
      (mkDat c χ).J k γ (fun v => gv v g • iP) * f ((fun v => gv v g • iP), x) := by
  have e1 : (mkDat c χ).act γ (fun v => gv v g • iP) = fun v => gv v (rr γ * g) • iP := funext fun v => by
    change (mkDat c χ).r v γ • gv v g • iP = _
    rw [map_mul, mul_smul, gv_rr c χ]
  have e4 : TR.infGL F 2 (rr γ * g) * finGL F 2 (jF F γ * x) = ratGL F 2 γ * (TR.infGL F 2 g * finGL F 2 x) := by
    rw [rat_eq, map_mul, map_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (TR.infGL F 2 g), TR.infGL_comm, mul_assoc]
  have e5 : ∀ v, j1 (k v) (gv v (rr γ * g)) iP = j1 (k v) ((mkDat c χ).r v γ) (gv v g • iP) * j1 (k v) (gv v g) iP :=
    fun v => by rw [map_mul, hb.1, gv_rr c χ]
  rw [e1, ← hf, ← hf, e4, hφ.left, Finset.prod_congr rfl fun v _ => e5 v, Finset.prod_mul_distrib]
  change _ = (∏ v, j1 (k v) ((mkDat c χ).r v γ) (gv v g • iP)) * _
  ring

theorem lev (k : InfinitePlace F → ℕ) (c : Pl F → ℕ) (ω : HChar F) (χ : Hc c →* ℂˣ) (hχ : IsChi c ω χ) (φ : TR.Sm F 2)
    (hcent : ∀ (z : Ideles F) (g : GA F 2), φ.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g)
    (hfix : ∀ u ∈ Kc c, TR.finRep F 2 u φ = φ)
    (f : X (InfinitePlace F) × GF F → ℂ) (hf : Rel k f φ.1) (g : GL (Fin 2) (TR.Rinf F)) (x : GF F) (h : Hc c) :
    f ((fun v => gv v g • iP), x * (h : GF F)) = ((χ h : ℂˣ) : ℂ) * f ((fun v => gv v g • iP), x) := by
  obtain ⟨⟨κ, hκ, z0, hz⟩, hv⟩ := hχ h
  have e5 : φ.1 (TR.infGL F 2 g * finGL F 2 x * finGL F 2 κ) = φ.1 (TR.infGL F 2 g * finGL F 2 x) :=
    congrArg (fun ψ : TR.Sm F 2 => ψ.1 (TR.infGL F 2 g * finGL F 2 x)) (hfix κ hκ)
  have e6 : TR.infGL F 2 g * finGL F 2 (x * (h : GF F)) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (finId F z0) * (TR.infGL F 2 g * finGL F 2 x * finGL F 2 κ) := by
    rw [hz, map_mul, map_mul, fin_zc, sc_comm]
    simp only [mul_assoc]
  rw [← hf, ← hf, hv κ hκ z0 hz, e6, hcent, e5, mul_assoc]

theorem bdd (hb : B1b) (k : InfinitePlace F → ℕ) (φ : TR.Sm F 2) (C : ℝ) (hC : ∀ g, ‖φ.1 g‖ ≤ C)
    (f : X (InfinitePlace F) × GF F → ℂ) (hf : Rel k f φ.1) (g : GL (Fin 2) (TR.Rinf F)) (x : GF F) :
    ‖f ((fun v => gv v g • iP), x)‖ * nrm k (fun v => gv v g • iP) ≤ C := by
  have e : ∀ v, ‖j1 (k v) (gv v g) iP‖ * |(gv v g • iP).1.im| ^ ((k v : ℝ) / 2) = 1 := fun v => by
    rw [hb.2.2.2.2.1]
    simp [iP]
  rw [← hf g x, norm_mul, nrm, norm_prod, mul_assoc, ← Finset.prod_mul_distrib]
  simp only [e, Finset.prod_const_one, mul_one]
  exact hC _

end UpperTheory.Esk.HyperbolicIntegrabilityLemmas

open UpperTheory.Esk in
theorem UpperTheory.Esk.hyperbolic_terms_integrable_proof : UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.H0 → UpperTheory.Esk.H1a → UpperTheory.Esk.H1b → UpperTheory.Esk.H1c → UpperTheory.Esk.H1 := by
  intro hb hc h0 h1a h1b h1c F _ _ _ k c ω χ hω hχ φ hφ hcusp
  obtain ⟨f, hf⟩ := h1a F k c ω φ hω hφ
  refine ⟨f, ⟨h1b F k c ω φ hω hφ f hf, fun γ z x => ?_, fun z x h => ?_, ?_⟩, hf⟩
  · obtain ⟨g, rfl⟩ := HeckeRelationLemmas.exists_g hc z
    exact HyperbolicIntegrabilityLemmas.aut hb k c χ φ hφ.aut f hf γ g x
  · obtain ⟨g, rfl⟩ := HeckeRelationLemmas.exists_g hc z
    by_cases h0φ : φ = 0
    · have e : ∀ g x, f (fun v => gv v g • iP, x) = 0 := fun g x => by rw [← hf g x, h0φ]; simp
      change f (_, x * (h : GF F)) = ((χ h : ℂˣ) : ℂ) * f (_, x)
      rw [e, e, mul_zero]
    obtain ⟨-, hfix, -⟩ := h0 F k c ω φ hφ h0φ
    exact HyperbolicIntegrabilityLemmas.lev k c ω χ hχ φ hφ.cent hfix f hf g x h
  · obtain ⟨C, hC⟩ := h1c F k c ω φ hω hφ hcusp
    refine ⟨C, fun z x => ?_⟩
    obtain ⟨g, rfl⟩ := HeckeRelationLemmas.exists_g hc z
    exact HyperbolicIntegrabilityLemmas.bdd hb k φ C hC f hf g x
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfGTerm
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.adelicTermLemmas

theorem term_v (k₀ t' cnt : ℕ) (hk : 2 ≤ k₀) (s τ δ U L : ℂ) (hs : s ≠ 0) (hδ : δ ≠ 0) (hδU : δ * U = L ^ cnt) (d tr : ℝ)
    (hd : 0 < d) (htr : (tr : ℂ) = s * τ) (hdet : (d : ℂ) = s ^ 2 * δ) :
    L ^ (t' * cnt) * -(((ch tr d (k₀ + 2 * t' - 1) * d ^ (1 - ((k₀ + 2 * t' : ℕ) : ℝ) / 2) : ℝ) : ℂ)) =
      (s ^ (k₀ - 2) * ((d ^ (1 - (k₀ : ℝ) / 2) : ℝ) : ℂ)) * -(ch τ δ (k₀ + 2 * t' - 1) * U ^ t') := by
  have e1 : ((ch tr d (k₀ + 2 * t' - 1) : ℝ) : ℂ) = s ^ (k₀ - 2 + 2 * t') * ch τ δ (k₀ + 2 * t' - 1) := by
    have h := ch_map Complex.ofRealHom tr d (k₀ + 2 * t' - 1)
    simp only [Complex.ofRealHom_eq_coe] at h
    rw [h, htr, hdet]
    have hk' : k₀ + 2 * t' - 1 = (k₀ - 2 + 2 * t') + 1 := by omega
    rw [hk', ch_hom]
  have e2 : ((d ^ (1 - ((k₀ + 2 * t' : ℕ) : ℝ) / 2) : ℝ) : ℂ) = ((d ^ (1 - (k₀ : ℝ) / 2) : ℝ) : ℂ) * ((s ^ 2 * δ) ^ t')⁻¹ := by
    have h : (1 - ((k₀ + 2 * t' : ℕ) : ℝ) / 2) = (1 - (k₀ : ℝ) / 2) + (-(t' : ℝ)) := by push_cast; ring
    rw [h, Real.rpow_add hd, Real.rpow_neg hd.le, Real.rpow_natCast, Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_pow, hdet]
  rw [Complex.ofReal_mul, e1, e2, mul_comm t' cnt, pow_mul, ← hδU, pow_add, mul_pow, mul_pow, ← pow_mul]
  field_simp

theorem list_prod_ofReal {α : Type*} (W : List α) (f : α → ℝ) : (W.map fun w => ((f w : ℝ) : ℂ)).prod = (((W.map f).prod : ℝ) : ℂ) := by
  induction W with
  | nil => simp
  | cons w W ih => simp [ih]

end UpperTheory.Esk.adelicTermLemmas

open UpperTheory.Esk.adelicTermLemmas Classical in
theorem UpperTheory.Esk.pf_GTerm : UpperTheory.Esk.GCh → UpperTheory.Esk.GUnit → UpperTheory.Esk.GMod → UpperTheory.Esk.GTerm := by
  intro hG hU hMod F _ _ _ l _ ι D c χ hc k₀ hk₀ N t ht W r hr hW n a hR γ x i hell hmem
  obtain ⟨k, hk, z, hkz⟩ := hc_decomp hmem
  have hrel1 : jF F γ * x * (k * zc F z) = x * a i := by rw [← hkz]; group
  have hrel2 : jF F γ = x * (a i * k⁻¹ * zc F z⁻¹) * x⁻¹ := by
    have hcz : k⁻¹ * zc F z⁻¹ = zc F z⁻¹ * k⁻¹ := Subgroup.mem_center_iff.1 (zc_center z⁻¹) k⁻¹
    have e : jF F γ = x * a i * (k * zc F z)⁻¹ * x⁻¹ := by rw [← hrel1]; group
    rw [e, mul_inv_rev, ← map_inv, ← hcz]
    simp only [mul_assoc]
  have hloc := fun v => loc D hU hc hr hW hR hk hrel2 v N
  choose τ δ U htr hdt hτ1 hδ1 hδr hU1 hδU hpow using hloc
  have hs0 : ∀ v, (D.ea v (z : Af F))⁻¹ ≠ 0 := fun v => inv_ne_zero ((z.isUnit.map (D.ea v)).ne_zero)
  have hσ : ∀ v (y : F), (((mkDat c χ).σ v y : ℝ) : ℂ) = v.embedding y := fun v y =>
    InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) y
  have hre : ∀ v (y : F), reAt v y = (mkDat c χ).σ v y := fun v y => by rw [reAt, ← hσ, Complex.ofReal_re]
  have hdpos : ∀ v, 0 < (mkDat c χ).σ v γ.val.det := fun v => by
    have := hell v
    nlinarith [sq_nonneg ((mkDat c χ).σ v γ.val.trace)]
  have hδ0 : ∀ v, δ v ≠ 0 := fun v h => by
    have h1 := hdt v
    rw [h, mul_zero, ← hσ] at h1
    exact (hdpos v).ne' (by exact_mod_cast h1)
  set A : ℝ := absF z with hA_def
  have hA : 0 < A := (Hm.absf F).1 z
  set Nw : ℝ := (W.map fun w => (normV w : ℝ)).prod with hNw
  have hp : ∏ v, (mkDat c χ).σ v γ.val.det = A ^ 2 * Nw := by
    rw [hA_def, hNw, ← prod_reAt hR hk hrel1]
    exact Finset.prod_congr rfl fun v _ => by rw [hre, abs_of_pos (hdpos v)]
  have hN : 0 < Nw := by
    have h1 : 0 < A ^ 2 * Nw := hp ▸ Finset.prod_pos fun v _ => hdpos v
    exact pos_of_mul_pos_right h1 (by positivity)
  have hreal : (W.map fun w => (normV w : ℝ) ^ ((k₀ : ℝ) / 2 - 1)).prod * ∏ v, (mkDat c χ).σ v γ.val.det ^ (1 - (k₀ : ℝ) / 2) =
      (A ^ (k₀ - 2))⁻¹ := by
    rw [Real.list_prod_map_rpow' W (fun w => (normV w : ℝ)) (fun _ _ => Nat.cast_nonneg _),
      Real.finsetProd_rpow _ _ (fun v _ => (hdpos v).le), hp, ← hNw]
    have e1 : (A ^ 2 * Nw) ^ (1 - (k₀ : ℝ) / 2) = (A ^ 2) ^ (1 - (k₀ : ℝ) / 2) * Nw ^ (1 - (k₀ : ℝ) / 2) :=
      Real.mul_rpow (by positivity) hN.le
    have e2 : Nw ^ ((k₀ : ℝ) / 2 - 1) * Nw ^ (1 - (k₀ : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add hN, show (k₀ : ℝ) / 2 - 1 + (1 - (k₀ : ℝ) / 2) = 0 by ring, Real.rpow_zero]
    have e3 : (A ^ 2) ^ (1 - (k₀ : ℝ) / 2) = (A ^ (k₀ - 2))⁻¹ := by
      rw [← Real.rpow_natCast_mul hA.le, show ((2 : ℕ) : ℝ) * (1 - (k₀ : ℝ) / 2) = -((k₀ - 2 : ℕ) : ℝ) by
        rw [Nat.cast_sub hk₀]; push_cast; ring, Real.rpow_neg hA.le, Real.rpow_natCast]
    rw [e1, ← e3]
    calc Nw ^ ((k₀ : ℝ) / 2 - 1) * ((A ^ 2) ^ (1 - (k₀ : ℝ) / 2) * Nw ^ (1 - (k₀ : ℝ) / 2))
        = (A ^ 2) ^ (1 - (k₀ : ℝ) / 2) * (Nw ^ ((k₀ : ℝ) / 2 - 1) * Nw ^ (1 - (k₀ : ℝ) / 2)) := by ring
      _ = (A ^ 2) ^ (1 - (k₀ : ℝ) / 2) := by rw [e2, mul_one]
  set Q : ℂ := (((A : ℂ) * ∏ v, D.ea v (z : Af F)) ^ (k₀ - 2))⁻¹ with hQ
  have key : ∀ t' : InfinitePlace F → ℕ, (W.map (nz D k₀ t')).prod * (mkDat c χ).orb (fun v => k₀ + 2 * t' v) γ =
      Q * ∏ v, -(ch (τ v) (δ v) (k₀ + 2 * t' v - 1) * U v ^ t' v) := by
    intro t'
    rw [nz_prod]
    simp only [Dat.orb]
    rw [mul_assoc, ← Finset.prod_mul_distrib]
    rw [Finset.prod_congr rfl fun v _ => term_v k₀ (t' v) (W.count (D.pl v)) hk₀ _ (τ v) (δ v) (U v) (l : ℂ) (hs0 v) (hδ0 v)
      (hδU v) _ _ (hdpos v) (by rw [hσ]; exact htr v) (by rw [hσ]; exact hdt v)]
    rw [Finset.prod_mul_distrib, ← mul_assoc]
    congr 1
    rw [Finset.prod_mul_distrib, list_prod_ofReal, mul_comm (∏ v, _ ^ (k₀ - 2)), ← mul_assoc, ← Complex.ofReal_prod,
      ← Complex.ofReal_mul, hreal, hQ, mul_pow, mul_inv, Finset.prod_pow, Finset.prod_inv_distrib, Complex.ofReal_inv,
      Complex.ofReal_pow, inv_pow]
  have hQ1 : nu ι Q = 1 := by
    rw [hQ, map_inv₀, map_pow, hA_def, (hMod F l ι D z).2, one_pow, inv_one]
  have hcong := fun v => local_cong (nu ι) hG (τ v) (δ v) (U v) (max (nu ι l ^ N) (nu ι l ^ r)) k₀ (t v) hk₀ (hτ1 v) (hδ1 v)
    ((hδr v).trans (le_max_right _ _)) ((hpow v (t v) (ht v)).1.trans (le_max_left _ _)) (hU1 v)
    ((hpow v (t v) (ht v)).2.trans (le_max_left _ _))
  obtain ⟨p1, p2, p3⟩ := val_prod_sub (nu ι) Finset.univ (fun v => -(ch (τ v) (δ v) (k₀ - 1)))
    (fun v => -(ch (τ v) (δ v) (k₀ + 2 * t v - 1) * U v ^ t v)) (max (nu ι l ^ N) (nu ι l ^ r))
    (fun v _ => by rw [Valuation.map_neg]; exact (hcong v).1) (fun v _ => by rw [Valuation.map_neg]; exact (hcong v).2.1)
    (fun v _ => by rw [neg_sub_neg, Valuation.map_sub_swap]; exact (hcong v).2.2)
  have h0 := key 0
  simp only [Pi.zero_apply, mul_zero, add_zero, pow_zero, mul_one] at h0
  rw [h0, key t]
  refine ⟨?_, ?_, ?_⟩
  · rw [map_mul, hQ1, one_mul]; exact p1
  · rw [map_mul, hQ1, one_mul]; exact p2
  · rw [← mul_sub, map_mul, hQ1, one_mul]; exact p3
end
end

