module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IndexNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.ExtChar
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

namespace UpperTheory.V.Z.Sym.Al.ExtChar

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem val_eq (x : kˣ) : valuation k (x : k) = uniformizer k ^ ord k x := by
  have h := UpperTheory.V.Hi.GlAx.val_div_ord x
  rw [Units.val_div_eq_div_val, map_div₀, UpperTheory.V.Hi.GlAx.val_zpow] at h
  exact (div_eq_one_iff_eq (zpow_pos UpperTheory.V.Hi.GlAx.unif_pos _).ne').1 h

private theorem sdom_of_exp (u : Fin n → kˣ) (e : Fin n → ℤ)
    (hv : ∀ i, valuation k (u i : k) = uniformizer k ^ e i) (he : ∀ i j, i < j → e j < e i) : Sig.SDom u := by
  intro i j hij
  rw [hv, hv]
  exact zpow_lt_zpow_right_of_lt_one₀ UpperTheory.V.Hi.GlAx.unif_pos uniformizer_lt_one (he i j hij)

private noncomputable def rho (n : ℕ) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℤ) : Fin n → kˣ := fun i => UpperTheory.V.Hi.unif k ^ (-(m * (i : ℕ)))

private theorem rho_sdom {m : ℤ} (hm : 0 < m) : Sig.SDom (rho n k m) := by
  refine sdom_of_exp _ (fun i => -(m * ((i : ℕ) : ℤ))) (fun i => UpperTheory.V.Hi.GlAx.val_zpow _) fun i j hij => ?_
  have : ((i : ℕ) : ℤ) < ((j : ℕ) : ℤ) := by exact_mod_cast hij
  nlinarith

private theorem sdom_mul {d d' : Fin n → kˣ} (h : Sig.SDom d) (h' : Sig.SDom d') : Sig.SDom (d * d') := by
  intro i j hij
  simp only [Pi.mul_apply, Units.val_mul, map_mul]
  exact mul_lt_mul'' (h i j hij) (h' i j hij) zero_le' zero_le'

private theorem sdom_mul_unit {d u : Fin n → kˣ} (h : Sig.SDom d) (hu : ∀ i, u i ∈ UpperTheory.V.Hi.Uo k) : Sig.SDom (d * u) := by
  intro i j hij
  have h1 : ∀ i, valuation k (u i : k) = 1 := hu
  simp only [Pi.mul_apply, Units.val_mul, map_mul, h1, mul_one]
  exact h i j hij

private theorem exists_div (t : Fin n → kˣ) : ∃ a b : Fin n → kˣ, Sig.SDom a ∧ Sig.SDom b ∧ t = a * b⁻¹ := by
  let B : ℤ := ∑ i, |ord k (t i)|
  have hB : ∀ i, |ord k (t i)| ≤ B := fun i =>
    Finset.single_le_sum (f := fun i => |ord k (t i)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hm : 0 < 2 * B + 1 := by omega
  refine ⟨t * rho n k (2 * B + 1), rho n k (2 * B + 1), ?_, rho_sdom hm, by simp⟩
  refine sdom_of_exp _ (fun i => ord k (t i) + -((2 * B + 1) * ((i : ℕ) : ℤ))) (fun i => ?_) fun i j hij => ?_
  · rw [Pi.mul_apply, Units.val_mul, map_mul, val_eq, rho, UpperTheory.V.Hi.GlAx.val_zpow,
      zpow_add₀ UpperTheory.V.Hi.GlAx.unif_pos.ne']
  · have h0 : ((i : ℕ) : ℤ) + 1 ≤ ((j : ℕ) : ℤ) := by exact_mod_cast hij
    have h1 := abs_le.1 (hB i)
    have h2 := abs_le.1 (hB j)
    nlinarith

private def P (n : ℕ) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    Submonoid (Fin n → kˣ) where
  carrier := {d | Sig.SDom d ∨ d = 1}
  one_mem' := Or.inr rfl
  mul_mem' := by
    rintro a b (ha | rfl) (hb | rfl)
    · exact Or.inl (sdom_mul ha hb)
    · simpa using Or.inl ha
    · simpa using Or.inl hb
    · simp

private theorem delta_unit (v : Fin n → kˣ) (hv : ∀ i, v i ∈ UpperTheory.V.Hi.Uo k) :
    (deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom v = 1 := by
  rw [MonoidHom.comp_apply, deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  have h : Matrix.GeneralLinearGroup.det (leviTorus k (Fin n) v a) = v a := congrFun ((leviTorus k (Fin n)).left_inv v) a
  erw [h]
  exact isUnram_absPow k _ _ (hv a)

end UpperTheory.V.Z.Sym.Al.ExtChar

open UpperTheory.V.Z.Sym.Al.ExtChar in
theorem UpperTheory.V.Z.Sym.Al.extChar :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (χ : (Fin n → kˣ) → ℂ), (∀ d, Sig.SDom d → χ d ≠ 0) → (∀ d d', Sig.SDom d → Sig.SDom d' → χ (d * d') = χ d * χ d') →
        (∀ d u, Sig.SDom d → (∀ i, u i ∈ Hi.Uo k) → χ (d * u) = χ d) →
        ∃ ψ : Fin n → kˣ →* ℂˣ, (∀ i, ∀ u ∈ Hi.Uo k, ψ i u = 1) ∧ ∀ d, Sig.SDom d → χ d = expo ψ d := by
  classical
  intro k _ _ _ _ n χ hne hmul hunit
  let f : (Fin n → kˣ) → ℂ := fun d => if d = 1 then 1 else χ d
  have hf : ∀ d, Sig.SDom d → f d = χ d := by
    intro d hd
    by_cases h1 : d = 1
    · subst h1
      have h2 := hmul 1 1 hd hd
      rw [mul_one] at h2
      have h3 : χ 1 = 1 := by
        have h4 := hne 1 hd
        exact mul_right_cancel₀ h4 (by rw [one_mul]; exact h2.symm)
      simp [f, h3]
    · simp [f, h1]
  have hf1 : f 1 = 1 := by simp [f]
  obtain ⟨θ, hθ, -⟩ := UpperTheory.V.AlgebraTools.monoidExt (Fin n → kˣ) ℂ (P n k) f
    (fun t => by
      obtain ⟨a, b, ha, hb, h⟩ := exists_div t
      exact ⟨a, Or.inl ha, b, Or.inl hb, h⟩)
    hf1
    (by
      rintro a (ha | rfl) b (hb | rfl)
      · rw [hf _ ha, hf _ hb, hf _ (sdom_mul ha hb), hmul _ _ ha hb]
      · rw [mul_one, hf1, mul_one]
      · rw [one_mul, hf1, one_mul]
      · rw [mul_one, hf1, mul_one])
    (by
      rintro a (ha | rfl)
      · rw [hf _ ha]
        exact (hne a ha).isUnit
      · rw [hf1]
        exact isUnit_one)
  have hθχ : ∀ d, Sig.SDom d → (θ d : ℂ) = χ d := fun d hd => (hθ d (Or.inl hd)).trans (hf d hd)
  have hθu : ∀ u : Fin n → kˣ, (∀ i, u i ∈ Hi.Uo k) → θ u = 1 := by
    intro u hu
    obtain ⟨a, -, ha, -, -⟩ := exists_div (1 : Fin n → kˣ)
    have h1 : θ (a * u) = θ a := Units.ext (by
      rw [hθχ _ (sdom_mul_unit ha hu), hθχ _ ha, hunit _ _ ha hu])
    rw [map_mul] at h1
    exact mul_left_cancel (h1.trans (mul_one _).symm)
  let D : (Fin n → kˣ) →* ℂˣ := (deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom
  have hsingle : ∀ (i : Fin n) (u : kˣ), u ∈ Hi.Uo k → ∀ j, (Pi.mulSingle i u : Fin n → kˣ) j ∈ Hi.Uo k := by
    intro i u hu j
    by_cases h : j = i
    · subst h; simpa using hu
    · rw [Pi.mulSingle_eq_of_ne h]; exact one_mem _
  refine ⟨fun i => (θ * D).comp (MonoidHom.mulSingle (fun _ : Fin n => kˣ) i), ?_, ?_⟩
  · intro i u hu
    simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.mulSingle_apply]
    rw [hθu _ (hsingle i u hu), delta_unit _ (hsingle i u hu), one_mul]
  · intro d hd
    have h1 : torusChar (fun i => (θ * D).comp (MonoidHom.mulSingle (fun _ : Fin n => kˣ) i)) d = θ d * D d := by
      rw [torusChar_apply]
      simp only [MonoidHom.comp_apply, MonoidHom.mulSingle_apply]
      rw [← map_prod, Finset.univ_prod_mulSingle, MonoidHom.mul_apply]
    rw [Dict.expo, h1, ← hθχ d hd]
    change (θ d : ℂ) = ((θ d * D d * (D d)⁻¹ : ℂˣ) : ℂ)
    rw [mul_inv_cancel_right]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Factor
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

noncomputable section

namespace UpperTheory.V.Z.Sym.Al.FactorizationTer

open GlobalTheory.SplitPts GlobalTheory.BCT.GlobLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem ua_ext {g h : UA E n} (h1 : cInf g = cInf h) (h2 : ∀ u, cLoc u g = cLoc u h) : g = h := by
  refine Subtype.ext (ga_ext h1 ?_)
  refine Units.ext (matAf_ext fun u => ?_)
  exact congrArg Units.val (h2 u)


open Classical in
private def idem (P : HeightOneSpectrum (𝓞 E) → Prop) : Af E :=
  ⟨fun u => if P u then 1 else 0, Filter.Eventually.of_forall fun u => by
    dsimp only
    split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

open Classical in
private theorem pLoc_idem (P : HeightOneSpectrum (𝓞 E) → Prop) (u : HeightOneSpectrum (𝓞 E)) :
    pLoc E u (idem P) = if P u then 1 else 0 := rfl

private def cutM (P : HeightOneSpectrum (𝓞 E) → Prop) (A : Matrix (Fin n) (Fin n) (Af E)) :
    Matrix (Fin n) (Fin n) (Af E) := idem P • A + (1 - idem P) • 1

private theorem map_cutM_pos {P : HeightOneSpectrum (𝓞 E) → Prop} (A : Matrix (Fin n) (Fin n) (Af E))
    {u : HeightOneSpectrum (𝓞 E)} (h : P u) :
    RingHom.mapMatrix (pLoc E u) (cutM P A) = RingHom.mapMatrix (pLoc E u) A := by
  ext i j
  simp [cutM, Matrix.add_apply, Matrix.smul_apply, pLoc_idem, h]

private theorem map_cutM_neg {P : HeightOneSpectrum (𝓞 E) → Prop} (A : Matrix (Fin n) (Fin n) (Af E))
    {u : HeightOneSpectrum (𝓞 E)} (h : ¬ P u) :
    RingHom.mapMatrix (pLoc E u) (cutM P A) = 1 := by
  have h0 : pLoc E u (idem P) = 0 := by rw [pLoc_idem, if_neg h]
  refine Matrix.ext fun i j => ?_
  change pLoc E u (idem P * A i j + (1 - idem P) * (1 : Matrix (Fin n) (Fin n) (Af E)) i j) =
    (1 : Matrix (Fin n) (Fin n) (u.adicCompletion E)) i j
  rw [map_add (f := _), map_mul, map_mul, map_sub, map_one, h0, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

private theorem cutM_mul (P : HeightOneSpectrum (𝓞 E) → Prop) {A B : Matrix (Fin n) (Fin n) (Af E)}
    (h : A * B = 1) : cutM P A * cutM P B = 1 := by
  refine matAf_ext fun u => ?_
  rw [map_mul, map_one]
  by_cases hu : P u
  · rw [map_cutM_pos _ hu, map_cutM_pos _ hu, ← map_mul, h, map_one]
  · rw [map_cutM_neg _ hu, map_cutM_neg _ hu, one_mul]

private def cut (P : HeightOneSpectrum (𝓞 E) → Prop) (k : GL (Fin n) (Af E)) : GL (Fin n) (Af E) where
  val := cutM P k.val
  inv := cutM P (k⁻¹).val
  val_inv := cutM_mul P (by simp)
  inv_val := cutM_mul P (by simp)

private theorem under_conj (u : HeightOneSpectrum (𝓞 E)) :
    (conjSrc (conjE E) u).under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E)) :=
  (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) u _).2
      (Or.inr (conjPl_self_conjSrc u))

private theorem exists_part (w : HeightOneSpectrum (𝓞 E)) (g : UA E n) :
    ∃ x : UA E n, cInf x = 1 ∧
      (∀ u, u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → cLoc u x = cLoc u g) ∧
      ∀ u, u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) → cLoc u x = 1 := by
  set P : HeightOneSpectrum (𝓞 E) → Prop := fun u =>
    u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) with hP
  set k : GL (Fin n) (Af E) := cut P (Matrix.GeneralLinearGroup.map (pFin E) g.1) with hk
  have hpos : ∀ u, P u → Matrix.GeneralLinearGroup.map (pLoc E u) k = cLoc u g := fun u hu =>
    Units.ext (map_cutM_pos _ hu)
  have hneg : ∀ u, ¬ P u → Matrix.GeneralLinearGroup.map (pLoc E u) k = 1 := fun u hu =>
    Units.ext (map_cutM_neg _ hu)
  have hmem : finGL E n k ∈ UA E n := by
    refine finGL_mem_UA k fun u => ?_
    by_cases hu : P u
    · have hc : P (conjSrc (conjE E) u) := (under_conj u).trans hu
      rw [hpos u hu, hpos _ hc]
      exact comp_eq g u
    · have hc : ¬ P (conjSrc (conjE E) u) := fun h => hu ((under_conj u).symm.trans h)
      rw [hneg u hu, hneg _ hc]
      simp
  have hloc : ∀ u, cLoc u (⟨_, hmem⟩ : UA E n) = Matrix.GeneralLinearGroup.map (pLoc E u) k := fun u => by
    change Matrix.GeneralLinearGroup.map ((pLoc E u).comp (pFin E)) (finGL E n k) = _
    exact Units.ext (congrArg (fun M : GL (Fin n) (Af E) => RingHom.mapMatrix (pLoc E u) M.val) (pFin_finGL k))
  exact ⟨⟨_, hmem⟩, pInf_finGL k, fun u hu => (hloc u).trans (hpos u hu),
    fun u hu => (hloc u).trans (hneg u hu)⟩

end UpperTheory.V.Z.Sym.Al.FactorizationTer

end

theorem UpperTheory.V.Z.Sym.Al.factor :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (w : Plc L),
        (∀ x ∈ locU n w, ∀ y ∈ away n w, x * y = y * x) ∧
        (∀ g : UA L n, ∃ x ∈ locU n w, ∃ y ∈ away n w, g = x * y) ∧
        (∀ w' : Plc L, w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)) → locU n w' ≤ away n w) ∧ infU L n ≤ away n w ∧
        (∀ x ∈ locU n w, x ∈ Kall (L := L) n ↔ cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n)) ∧
        ∀ x ∈ locU n w, ∀ y ∈ away n w, (x * y ∈ Kall (L := L) n ↔ x ∈ Kall (L := L) n ∧ y ∈ Kall (L := L) n) := by
  intro L _ _ _ n w
  have hfin : ∀ {x : UA L n}, x ∈ locU n w → cInf x = 1 := fun hx => (Subgroup.mem_inf.1 hx).1
  have hout : ∀ {x : UA L n}, x ∈ locU n w → ∀ u : Plc L, u.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)) →
      cLoc u x = 1 := fun hx u hu =>
    MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u) hu)
  have hin : ∀ {y : UA L n}, y ∈ away n w → ∀ u : Plc L, u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L)) →
      cLoc u y = 1 := fun hy u hu =>
    MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hy u) hu)
  have haway : ∀ {y : UA L n}, (∀ u : Plc L, u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L)) → cLoc u y = 1) →
      y ∈ away n w := fun h =>
    Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => MonoidHom.mem_ker.2 (h u hu)
  have hK : ∀ {x : UA L n}, x ∈ Kall (L := L) n → ∀ u : Plc L, cLoc u x ∈ GlobalTheory.LFun.KGL u (n := n) := fun hx u =>
    Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u)
  have hKmk : ∀ {x : UA L n}, x ∈ finU (E := L) (n := n) → (∀ u : Plc L, cLoc u x ∈ GlobalTheory.LFun.KGL u (n := n)) → x ∈ Kall (L := L) n :=
    fun h1 h2 => Subgroup.mem_inf.2 ⟨h1, Subgroup.mem_iInf.2 fun u => Subgroup.mem_comap.2 (h2 u)⟩
  have hKf : ∀ {x : UA L n}, x ∈ Kall (L := L) n → x ∈ finU (E := L) (n := n) := fun hx => (Subgroup.mem_inf.1 hx).1
  refine ⟨fun x hx y hy => ?_, fun g => ?_, fun w' hw' x hx => ?_, fun x hx => ?_, fun x hx => ⟨fun h => hK h w, fun h => ?_⟩,
    fun x hx y hy => ⟨fun h => ?_, fun h => mul_mem h.1 h.2⟩⟩
  · refine FactorizationTer.ua_ext ?_ fun u => ?_
    · rw [map_mul, map_mul, hfin hx, one_mul, mul_one]
    · rw [map_mul, map_mul]
      by_cases hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
      · rw [hin hy u hu, one_mul, mul_one]
      · rw [hout hx u hu, one_mul, mul_one]
  · obtain ⟨x, h1, h2, h3⟩ := FactorizationTer.exists_part w g
    refine ⟨x, Subgroup.mem_inf.2 ⟨h1, Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu =>
      MonoidHom.mem_ker.2 (h3 u hu)⟩, x⁻¹ * g, haway fun u hu => ?_, by group⟩
    rw [map_mul, map_inv, h2 u hu, inv_mul_cancel]
  · refine haway fun u hu => ?_
    exact MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u)
      (by rw [hu]; exact hw'.symm))
  · refine haway fun u _ => ?_
    have h : Matrix.GeneralLinearGroup.map (pFin L) x.1 = 1 := hx
    have h' := congrArg (Matrix.GeneralLinearGroup.map (pLoc L u)) h
    rw [map_one] at h'
    exact h'
  · refine hKmk (Subgroup.mem_inf.1 hx).1 fun u => ?_
    by_cases hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
    · rcases GlobalTheory.BCT.GlobLev.eq_or_eq_conjSrc hu with e | e
      · subst e
        exact h
      · subst e
        exact GlobalTheory.BCT.GlobLev.integral_conjSrc x w h
    · rw [hout hx u hu]
      exact one_mem _
  · have hf : cInf (x * y) = 1 := hKf h
    rw [map_mul, hfin hx, one_mul] at hf
    refine ⟨hKmk (Subgroup.mem_inf.1 hx).1 fun u => ?_, hKmk hf fun u => ?_⟩
    · by_cases hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
      · have := hK h u
        rwa [map_mul, hin hy u hu, mul_one] at this
      · rw [hout hx u hu]
        exact one_mem _
    · by_cases hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
      · rw [hin hy u hu]
        exact one_mem _
      · have := hK h u
        rwa [map_mul, hout hx u hu, one_mul] at this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.IsoCopy
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

private theorem isoCopy_struct {H T M : Type} [Group H] [AddCommGroup T] [Module ℂ T] [AddCommGroup M] [Module ℂ M]
    (τ : Representation ℂ H T) (μ : Representation ℂ H M) (hτ : τ.IsIrreducible)
    (hsup : (⨆ f : {f : T →ₗ[ℂ] M // ∀ h x, f (τ h x) = μ h (f x)}, LinearMap.range f.1) = ⊤) :
    IsSemisimpleModule (MonoidAlgebra ℂ H) μ.asModule ∧
      IsIsotypicOfType (MonoidAlgebra ℂ H) μ.asModule τ.asModule := by
  have hS : IsSimpleModule (MonoidAlgebra ℂ H) τ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule τ).1 hτ
  let F : {f : T →ₗ[ℂ] M // ∀ h x, f (τ h x) = μ h (f x)} →
      (τ.asModule →ₗ[MonoidAlgebra ℂ H] μ.asModule) := fun f =>
    Representation.IntertwiningMap.equivLinearMapAsModule τ μ
      (f.1.intertwiningMap_of_isIntertwiningMap τ μ f.2)
  have hle : ∀ f, LinearMap.range (F f) ≤ isotypicComponent (MonoidAlgebra ℂ H) μ.asModule τ.asModule := by
    intro f
    rcases LinearMap.injective_or_eq_zero (F f) with hi | h0
    · exact le_sSup ⟨(LinearEquiv.ofInjective (F f) hi).symm⟩
    · simp [h0]
  have htop : isotypicComponent (MonoidAlgebra ℂ H) μ.asModule τ.asModule = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : ∀ y : M, y ∈ (⨆ f : {f : T →ₗ[ℂ] M // ∀ h x, f (τ h x) = μ h (f x)}, LinearMap.range f.1) := fun y => by
      rw [hsup]; exact Submodule.mem_top
    refine Submodule.iSup_induction _
      (motive := fun y : M => (y : μ.asModule) ∈ isotypicComponent (MonoidAlgebra ℂ H) μ.asModule τ.asModule)
      (hx x) ?_ ?_ ?_
    · rintro f _ ⟨t, rfl⟩
      exact hle f ⟨t, rfl⟩
    · exact Submodule.zero_mem _
    · intro a b ha hb
      exact Submodule.add_mem _ ha hb
  have hss : IsSemisimpleModule (MonoidAlgebra ℂ H) (isotypicComponent (MonoidAlgebra ℂ H) μ.asModule τ.asModule) :=
    inferInstance
  rw [htop] at hss
  exact ⟨IsSemisimpleModule.congr (Submodule.topEquiv (R := MonoidAlgebra ℂ H) (M := μ.asModule)).symm,
    IsIsotypicOfType.of_isotypicComponent_eq_top htop⟩

theorem UpperTheory.V.Z.Sym.Al.isoCopy :
    ∀ (H T M : Type) [Group H] [AddCommGroup T] [Module ℂ T] [AddCommGroup M] [Module ℂ M] (τ : Representation ℂ H T) (μ : Representation ℂ H M),
        τ.IsIrreducible → (⨆ f : {f : T →ₗ[ℂ] M // ∀ h x, f (τ h x) = μ h (f x)}, LinearMap.range f.1) = ⊤ →
        (∀ v : M, v ≠ 0 → ∃ p : M →ₗ[ℂ] T, (∀ h x, p (μ h x) = τ h (p x)) ∧ p v ≠ 0) ∧
        ∀ (N I : Type) [AddCommGroup N] [Module ℂ N] [Finite I] (ν : Representation ℂ H N) (q : I → N →ₗ[ℂ] M),
          (∀ i h x, q i (ν h x) = μ h (q i x)) → (∀ x, (∀ i, q i x = 0) → x = 0) → Nontrivial N →
          ∃ f : T →ₗ[ℂ] N, f ≠ 0 ∧ ∀ h x, f (τ h x) = ν h (f x) := by
  intro H T M _ _ _ _ _ τ μ hτ hsup
  obtain ⟨hss, hiso⟩ := isoCopy_struct τ μ hτ hsup
  refine ⟨fun v hv => ?_, fun N I _ _ _ ν q hq hsep hN => ?_⟩
  · obtain ⟨ι, ⟨e⟩⟩ := hiso.linearEquiv_finsupp
    have hev : e (v : μ.asModule) ≠ 0 := fun h => hv (e.map_eq_zero_iff.1 h)
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hev
    let P : μ.asModule →ₗ[MonoidAlgebra ℂ H] τ.asModule :=
      (Finsupp.lapply i).comp e.toLinearMap
    let p := (Representation.IntertwiningMap.equivLinearMapAsModule μ τ).symm P
    exact ⟨p.toLinearMap, fun h x => Representation.IntertwiningMap.isIntertwining _ _ p h x, hi⟩
  · let Q : I → (ν.asModule →ₗ[MonoidAlgebra ℂ H] μ.asModule) := fun i =>
      Representation.IntertwiningMap.equivLinearMapAsModule ν μ
        ((q i).intertwiningMap_of_isIntertwiningMap ν μ (hq i))
    have hinj : Function.Injective (LinearMap.pi Q) := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro x hx
      exact hsep x fun i => congrFun hx i
    have hNs : IsSemisimpleModule (MonoidAlgebra ℂ H) ν.asModule :=
      IsSemisimpleModule.of_injective _ hinj
    haveI : Nontrivial ν.asModule := hN
    obtain ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule (MonoidAlgebra ℂ H) ν.asModule)
    rw [← isSimpleModule_iff_isAtom] at hS
    haveI := hS
    haveI := IsSimpleModule.nontrivial (MonoidAlgebra ℂ H) S
    obtain ⟨s, hs⟩ := exists_ne (0 : S)
    obtain ⟨i, hi⟩ : ∃ i, Q i s ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hs (Subtype.ext (hsep s.1 fun i => hc i))
    have hne : (Q i).comp S.subtype ≠ 0 := fun h => hi (LinearMap.congr_fun h s)
    have hj : Function.Injective ((Q i).comp S.subtype) :=
      (LinearMap.injective_or_eq_zero _).resolve_right hne
    let e1 := LinearEquiv.ofInjective _ hj
    haveI : IsSimpleModule (MonoidAlgebra ℂ H) (LinearMap.range ((Q i).comp S.subtype)) := IsSimpleModule.congr e1.symm
    obtain ⟨e2⟩ := hiso (LinearMap.range ((Q i).comp S.subtype))
    let G : τ.asModule →ₗ[MonoidAlgebra ℂ H] ν.asModule :=
      S.subtype.comp (e1.symm.toLinearMap.comp e2.symm.toLinearMap)
    let g := (Representation.IntertwiningMap.equivLinearMapAsModule τ ν).symm G
    refine ⟨g.toLinearMap, ?_, fun h x => Representation.IntertwiningMap.isIntertwining _ _ g h x⟩
    intro h0
    have : IsSimpleModule (MonoidAlgebra ℂ H) τ.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule τ).1 hτ
    haveI := IsSimpleModule.nontrivial (MonoidAlgebra ℂ H) τ.asModule
    obtain ⟨t, ht⟩ := exists_ne (0 : τ.asModule)
    have hG : G t = 0 := LinearMap.congr_fun h0 t
    have : (e1.symm (e2.symm t) : S) = 0 := Subtype.ext hG
    have hz : e2.symm t = 0 := e1.symm.injective (this.trans e1.symm.map_zero.symm)
    exact ht (e2.symm.injective (hz.trans e2.symm.map_zero.symm))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.OpenLev
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

theorem UpperTheory.V.Z.Sym.Al.openLev :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (π : Submodule ℂ (UA L n → ℂ)), IsAutRepU π → ∀ φ : UA L n → V, CoefIn φ π →
        ∃ U : Subgroup (UA L n), IsOpen {x : finU (E := L) (n := n) | (x : UA L n) ∈ U} ∧ ∀ u ∈ U, ∀ g, φ (g * u) = φ g := by
  intro L _ _ _ n V _ _ _ π hπ φ hc
  let U : Subgroup (UA L n) :=
    { carrier := {u | ∀ g, φ (g * u) = φ g}
      one_mem' := fun g => by rw [mul_one]
      mul_mem' := fun {a b} ha hb g => by rw [← mul_assoc, hb, ha]
      inv_mem' := fun {a} ha g => by rw [← ha, inv_mul_cancel_right] }
  refine ⟨U, ?_, fun u hu => hu⟩
  let b := Module.finBasis ℂ V
  have e : {x : finU (E := L) (n := n) | (x : UA L n) ∈ U} = ⋂ i, {k : finU (E := L) (n := n) | RU L n k (b.coord i ∘ φ) = b.coord i ∘ φ} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    refine ⟨fun h i => funext fun g => congrArg (b.coord i) (h g), fun h g => b.ext_elem fun i => congrFun (h i) g⟩
  rw [e]
  exact isOpen_iInter_of_finite fun i => (hπ.aut _ (hc _)).level
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.SmoothDepth
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

theorem UpperTheory.V.Z.Sym.Al.smoothDepth :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (χ : kˣ →* ℂˣ), IsSmoothChar χ → ∃ c₀ : ℕ, ∀ c ≥ c₀, ∀ u ∈ Hi.Uc k (c + 1), χ u = 1 := by
  intro k _ _ _ _ χ hχ
  have hopen : IsOpen (χ.ker : Set kˣ) := hχ
  obtain ⟨U, hU, hUe⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.mp hopen
  have h1U : (1 : k) ∈ U := by
    have h : (1 : kˣ) ∈ Units.val ⁻¹' U := by
      rw [hUe]
      exact χ.ker.one_mem
    exact h
  obtain ⟨γ, hγ⟩ := IsValuativeTopology.mem_nhds_iff.mp (hU.mem_nhds h1U)
  have hu1 : uniformizer k < 1 := uniformizer_lt_one
  obtain ⟨c₀, hc₀⟩ := exists_pow_lt₀ hu1 γ
  refine ⟨c₀, fun c hc u hu => ?_⟩
  obtain ⟨-, hv⟩ := Sig.mem_Uc.mp hu
  have hlt : valuation k ((u : k) - 1) < γ :=
    calc valuation k ((u : k) - 1) ≤ uniformizer k ^ ((c + 1 : ℕ) : ℤ) := hv
      _ = uniformizer k ^ (c + 1) := zpow_natCast _ _
      _ ≤ uniformizer k ^ c₀ := pow_le_pow_right_of_le_one' hu1.le (by omega)
      _ < γ := hc₀
  have hmem : (u : k) ∈ U := hγ ⟨(u : k) - 1, hlt, by ring⟩
  have h : u ∈ Units.val ⁻¹' U := hmem
  rw [hUe] at h
  exact h
end

