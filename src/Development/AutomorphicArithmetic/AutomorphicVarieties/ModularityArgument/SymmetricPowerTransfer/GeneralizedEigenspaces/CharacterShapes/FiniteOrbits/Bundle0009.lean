module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.UaFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0699
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.LocalLevelOutsideSigma

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.CongEx
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So.CongruenceExistence

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

private theorem memK {w : Plc L} (h : GL (Fin n) (Kw w)) : h ∈ GlobalTheory.LFun.KGL w (n := n) ↔
    (∀ i j, h.1 i j ∈ w.adicCompletionIntegers L) ∧ ∀ i j, (h⁻¹).1 i j ∈ w.adicCompletionIntegers L := by
  rw [GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff]; rfl

private theorem memO {x : Af L} : x ∈ UpperTheory.V.Af.Ohat L ↔ ∀ w : Plc L, pLoc L w x ∈ w.adicCompletionIntegers L := by
  rw [UpperTheory.V.Af.Ohat, Subring.mem_iInf]; rfl

private def fp : UA L n →* GL (Fin n) (Af L) :=
  (Matrix.GeneralLinearGroup.map (pFin L)).comp (UA L n).subtype

private theorem cLoc_val (w : Plc L) (x : UA L n) (i j : Fin n) :
    (cLoc w x).1 i j = pLoc L w ((fp x).1 i j) := rfl

private theorem cLoc_inv_val (w : Plc L) (x : UA L n) (i j : Fin n) :
    ((cLoc w x)⁻¹).1 i j = pLoc L w (((fp x)⁻¹).1 i j) := by
  rw [← map_inv, ← map_inv]; rfl

private theorem pLoc_one (w : Plc L) (i j : Fin n) :
    pLoc L w ((1 : Matrix (Fin n) (Fin n) (Af L)) i j) = (1 : Matrix (Fin n) (Fin n) (Kw w)) i j := by
  simp only [Matrix.one_apply]; split_ifs <;> simp

private theorem mem_iff {m : ℕ} (hm : m ≠ 0) (x : UA L n) :
    (x ∈ finU (E := L) (n := n) ∧ fp x ∈ UpperTheory.V.Af.KLev L n m) ↔
      x ∈ Kall L n ∧ ∀ w i j, ∃ a ∈ w.adicCompletionIntegers L, (mL w x - 1) i j = (m : Kw w) * a := by
  have hd : ∀ (w : Plc L) (i j : Fin n), (mL w x - 1) i j =
      pLoc L w ((fp x).1 i j - (1 : Matrix (Fin n) (Fin n) (Af L)) i j) := fun w i j => by
    rw [map_sub, pLoc_one, Matrix.sub_apply]; rfl
  constructor
  · rintro ⟨hf, hk⟩
    obtain ⟨h1, h2, h3⟩ := UpperTheory.V.Af.mem_KLev.1 hk
    refine ⟨⟨hf, Subgroup.mem_iInf.2 fun w => (memK _).2 ⟨fun i j => ?_, fun i j => ?_⟩⟩, fun w i j => ?_⟩
    · rw [cLoc_val]; exact memO.1 (h1 i j) w
    · rw [cLoc_inv_val]; exact memO.1 (h2 i j) w
    · obtain ⟨y, hy, e⟩ := h3 i j
      refine ⟨pLoc L w y, memO.1 hy w, ?_⟩
      rw [hd, show (fp x).1 i j - (1 : Matrix (Fin n) (Fin n) (Af L)) i j = (m : Af L) * y from e, map_mul, map_natCast]
  · rintro ⟨⟨hf, hK⟩, hc⟩
    have hK' : ∀ w : Plc L, cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n) := fun w => Subgroup.mem_iInf.1 hK w
    have hm' : (m : L) ≠ 0 := Nat.cast_ne_zero.2 hm
    set u : Af L := algebraMap L (Af L) (m : L)⁻¹ with hu'
    have hu : u * (m : Af L) = 1 := by
      rw [hu', ← map_natCast (algebraMap L (Af L)), ← map_mul, inv_mul_cancel₀ hm', map_one]
    refine ⟨hf, UpperTheory.V.Af.mem_KLev.2 ⟨fun i j => memO.2 fun w => ?_, fun i j => memO.2 fun w => ?_, fun i j =>
      ⟨u * ((fp x).1 i j - (1 : Matrix (Fin n) (Fin n) (Af L)) i j), memO.2 fun w => ?_, ?_⟩⟩⟩
    · rw [← cLoc_val]; exact ((memK _).1 (hK' w)).1 i j
    · rw [← cLoc_inv_val]; exact ((memK _).1 (hK' w)).2 i j
    · obtain ⟨a, ha, e⟩ := hc w i j
      rw [map_mul, ← hd, e, ← mul_assoc]
      have : pLoc L w u * (m : Kw w) = 1 := by
        have := congrArg (pLoc L w) hu
        rwa [map_mul, map_natCast, map_one] at this
      rwa [this, one_mul]
    · rw [← mul_assoc, mul_comm _ u, hu, one_mul]

private def cong (m : ℕ) : Subgroup (UA L n) := finU (E := L) (n := n) ⊓ (UpperTheory.V.Af.KLev L n m).comap fp

private theorem isCong {m : ℕ} (hm : m ≠ 0) : IsCong m (cong (L := L) (n := n) m) := fun x => mem_iff hm x

private theorem isLevel {m : ℕ} (hm : m ≠ 0) : IsLevel (cong (L := L) (n := n) m) := by
  refine ⟨fun x hx => ((isCong hm x).1 hx).1, ?_⟩
  have hc : Continuous fun x : finU (E := L) (n := n) => fp (x : UA L n) :=
    GlobalTheory.CuspRep.continuous_mapFin.comp (continuous_subtype_val.comp continuous_subtype_val)
  convert (UpperTheory.V.Af.isOpen_KLev (F := L) (n := n) (M := m) (Nat.one_le_iff_ne_zero.2 hm)).preimage hc using 1
  ext x
  exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩

private theorem trans_int {w : Plc L} {i j : Fin n} {c : Kw w} (hc : c ∈ w.adicCompletionIntegers L) (a b : Fin n) :
    Matrix.transvection i j c a b ∈ w.adicCompletionIntegers L := by
  rw [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  refine add_mem ?_ ?_
  · split_ifs
    · exact one_mem _
    · exact zero_mem _
  · split_ifs
    · exact hc
    · exact zero_mem _

private def el {w : Plc L} {i j : Fin n} (h : i ≠ j) : GL (Fin n) (Kw w) :=
  ⟨Matrix.transvection i j 1, Matrix.transvection i j (-1),
    by rw [Matrix.transvection_mul_transvection_same _ _ h]; simp,
    by rw [Matrix.transvection_mul_transvection_same _ _ h]; simp⟩

private theorem el_mem {w : Plc L} {i j : Fin n} (h : i ≠ j) : el (w := w) h ∈ GlobalTheory.LFun.KGL w (n := n) :=
  (memK _).2 ⟨fun a b => trans_int (one_mem _) a b, fun a b => trans_int (neg_mem (one_mem _)) a b⟩

private theorem last {m : ℕ} (hn : 2 ≤ n) (w : Plc L) (hw : IsSplitAt w)
    (hle : locU n w ⊓ Kall L n ≤ cong (L := L) (n := n) m) (hm : m ≠ 0) : (m : 𝓞 L) ∉ w.asIdeal := by
  intro hmw
  obtain ⟨h1, -, -, -, -, -, -, h8⟩ := UpperTheory.V.Z.Sym.Dict.Br.uaFacts L n
  obtain ⟨hl, hc, -, -⟩ := h1 w hw
  have hij : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  set g : GL (Fin n) (Kw w) := el hij with hg
  have hx := hl g
  have hK : secW n w g ∈ Kall L n := by
    refine ⟨hx.1, Subgroup.mem_iInf.2 fun u => ?_⟩
    by_cases hu : un u = un w
    · refine h8 w hw _ ?_ u hu
      rw [hc]; exact el_mem hij
    · have : secW n w g ∈ (cLoc (E := L) (n := n) u).ker :=
        Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.2 u) hu
      exact Subgroup.mem_comap.2 (by rw [MonoidHom.mem_ker.1 this]; exact one_mem _)
  obtain ⟨a, ha, e⟩ := ((isCong hm _).1 (hle ⟨hx, hK⟩)).2 w ⟨0, by omega⟩ ⟨1, by omega⟩
  have e1 : (mL w (secW n w g) - 1) ⟨0, by omega⟩ ⟨1, by omega⟩ = 1 := by
    rw [mL, hc]
    simp [g, el, Matrix.transvection, Matrix.single_apply]
  rw [e1] at e
  have hv : Valued.v ((m : Kw w)) < 1 := by
    have h0 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) w (m : 𝓞 L)).2 hmw
    have e2 : (m : Kw w) = algebraMap L (Kw w) (algebraMap (𝓞 L) L (m : 𝓞 L)) := by simp
    rw [e2]
    first
      | (rw [HeightOneSpectrum.algebraMap_adicCompletion, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact h0)
      | (rw [HeightOneSpectrum.algebraMap_adicCompletion, HeightOneSpectrum.valuedAdicCompletion_eq_valuation]; exact h0)
      | (erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact h0)
  have ha' : Valued.v a ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ha
  have := congrArg Valued.v e
  rw [map_one, map_mul] at this
  have h3 : Valued.v (m : Kw w) * Valued.v a < 1 := by
    calc _ ≤ Valued.v (m : Kw w) * 1 := by gcongr
      _ < 1 := by simpa using hv
  exact absurd this h3.ne'

end UpperTheory.V.Z.Sym.So.CongruenceExistence

open UpperTheory.V.Z.Sym.So.CongruenceExistence in
theorem UpperTheory.V.Z.Sym.So.congEx :
    UpperTheory.V.Z.Sym.So.CongEx := by
  intro L _ _ _ n m hm
  exact ⟨cong m, isCong hm, isLevel hm, fun hn w hw hle => last hn w hw hle hm⟩

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.DcAt
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.So.dcAt :
    UpperTheory.V.Z.Sym.So.DcAt := by
  intro L _ _ _ n U₀ S VL hP w hw hF d
  obtain ⟨hsec, hcomm, -, -, -, -, hcomp, hK⟩ := UpperTheory.V.Z.Sym.Dict.Br.uaFacts L n
  have hsp : IsSplitAt w := hP.split w hw
  obtain ⟨hloc, hcl, -, hsecx⟩ := hsec w hsp
  obtain ⟨-, -, -, -, -, hfin⟩ := UpperTheory.V.Z.Sym.Sig.finFacts (Kw w) (VL w)
  obtain ⟨hH, -, -, hJK⟩ := hfin n
  have hKO : GlobalTheory.SplitWeil.KO (Kw w) (Fin n) = GlobalTheory.LFun.KGL w (n := n) := GlobalTheory.SmGL.SphCompletion.KO_completion w n
  have hoff : ∀ (h : GL (Fin n) (Kw w)) (u : Plc L), un u ≠ un w → cLoc u (secW n w h) = 1 := fun h u e =>
    Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (hloc h).2 u) e
  have h2 : ∀ u ∈ lev U₀ S VL, cLoc w u ∈ (VL w).J n ∧ ∀ h, u * (secW n w (cLoc w u))⁻¹ * secW n w h =
      secW n w h * (u * (secW n w (cLoc w u))⁻¹) := fun u hu => by
    refine ⟨Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hu.2 w) hw, fun h => ?_⟩
    obtain ⟨a, ha, hau⟩ := hcomp w u (hF.1 hu.1).1
    have ea : secW n w (cLoc w u) = a := by rw [← hau w rfl, ← hsecx a ha]
    have hy : ∀ u', un u' = un w → cLoc u' (u * (secW n w (cLoc w u))⁻¹) = 1 := fun u' e => by
      rw [map_mul, map_inv, ea, hau u' e, mul_inv_cancel]
    exact (hcomm w _ (hloc h) _ hy).symm.eq
  have h3 : ∀ h ∈ (VL w).J n, secW n w h ∈ lev U₀ S VL := fun h hh => by
    refine ⟨hF.2 w (Finset.mem_singleton_self w) ⟨hloc h, ⟨(hloc h).1, Subgroup.mem_iInf.2 fun u => ?_⟩⟩, ?_⟩
    · by_cases e : un u = un w
      · refine hK w hsp _ ?_ u e
        rw [hcl, ← hKO]
        exact hJK hh
      · rw [Subgroup.mem_comap, hoff h u e]
        exact one_mem _
    · refine Subgroup.mem_iInf.2 fun w' => Subgroup.mem_iInf.2 fun hw' => ?_
      by_cases e : w' = w
      · subst e
        rw [Subgroup.mem_comap, hcl]
        exact hh
      · rw [Subgroup.mem_comap, hoff h w' fun e' => e (hP.inj hw' hw e')]
        exact one_mem _
  have main := fun (V : Type) [AddCommGroup V] [Module ℂ V] =>
    UpperTheory.V.Z.Sym.So.dcLocal _ _ V (secW n w) (cLoc w) ((VL w).J n) (lev U₀ S VL) hcl h2 h3 (Sig.dg d) (hH _)
  refine ⟨(main ℂ).1, fun V _ _ φ hφ c => ?_⟩
  unfold EigAt
  rw [(main V).2 φ hφ]

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.ExpoMap
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

section SlopeTestRemainingChoices

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {B : Bridge L} (T : Spl B)
  {S : Finset (Plc L)} {VL : ∀ w : Plc L, Lev (Kw w)} {A : SD B.Δ}

private theorem eU_congr {K : Type} [Field K] {Δ s s' : K} (e : s = s') (h : s * s = Δ) (h' : s' * s' = Δ) :
    eU h = eU h' := by subst e; rfl

private theorem eD_congr {K : Type} [Field K] {Δ s s' : K} (e : s = s') (h : s * s = Δ) (h' : s' * s' = Δ) :
    eD h = eD h' := by subst e; rfl

private theorem map_dg {k k' : Type} [Field k] [Field k'] {n : ℕ} (i : k ≃+* k') (d : Fin n → kˣ) :
    Matrix.GeneralLinearGroup.map (i : k →+* k') (diagT k (Fin n) d) =
      diagT k' (Fin n) fun a => Units.map (i : k →* k') (d a) := by
  ext a b
  simp only [Matrix.GeneralLinearGroup.map_apply, val_diagT]
  by_cases h : a = b
  · subst h; simp
  · simp [Matrix.diagonal_apply_ne _ h]

private theorem map_inj {k k' : Type} [Field k] [Field k'] {n : ℕ} (i : k ≃+* k') :
    Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin n) (i : k →+* k')) := by
  intro g g' h
  ext a b
  have := congrArg (fun x : GL (Fin n) k' => (x : Matrix (Fin n) (Fin n) k') a b) h
  simpa using this

private theorem levCore (hF : Fit T S VL A) {n : ℕ} (x : UA L n) (hx : x ∈ finU (E := L) (n := n))
    (P : Pl (Lp L) → Prop) (E : ∀ v, v ∈ A.Sg → GL (Fin n) (Kv v))
    (hK : ∀ v, P v ↔ ∀ w, un w = v → cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n))
    (hE : ∀ w (_ : w ∈ S) (h : IsSplitAt w) (hv : un w ∈ A.Sg),
      cLoc w x = Matrix.GeneralLinearGroup.map ((T w h).i : Kv (un w) →+* Kw w) (E (un w) hv)) :
    ((∀ v (h : v ∈ A.Sg), E v h ∈ (A.V v).J n) ∧ ∀ v ∉ A.Sg, P v) ↔ x ∈ lev (Kall (L := L) n) S VL := by
  have memL : x ∈ lev (Kall (L := L) n) S VL ↔
      (x ∈ finU (E := L) (n := n) ∧ ∀ w, cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n)) ∧ ∀ w ∈ S, cLoc w x ∈ (VL w).J n := by
    simp [lev, Kall, Subgroup.mem_inf, Subgroup.mem_iInf]
  rw [memL]
  have loc : ∀ w (hw : w ∈ S) (h : IsSplitAt w) (hv : un w ∈ A.Sg),
      cLoc w x ∈ (VL w).J n ↔ E (un w) hv ∈ (A.V (un w)).J n := by
    intro w hw h hv
    rw [hE w hw h hv]
    exact (T w h).J _ _ (hF.c w hw) (hF.H w hw h) n _
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨hx, fun w => ?_⟩, fun w hw => ?_⟩
    · by_cases hv : un w ∈ A.Sg
      · obtain ⟨w0, hw0, e⟩ := (hF.sg _).1 hv
        have sp := hF.pl.split w0 hw0
        have hv0 : un w0 ∈ A.Sg := e ▸ hv
        have hk : cLoc w0 x ∈ GlobalTheory.LFun.KGL w0 (n := n) := by
          rw [hE w0 hw0 sp hv0]
          exact ((T w0 sp).K n _).2 (((Sig.finFacts _ (A.V (un w0))).2.2.2.2.2 n).2.2.2 (h1 _ hv0))
        exact (Br.uaFacts L n).2.2.2.2.2.2.2 w0 sp x hk w e.symm
      · exact (hK _).1 (h2 _ hv) w rfl
    · exact (loc w hw (hF.pl.split w hw) ((hF.sg _).2 ⟨w, hw, rfl⟩)).2 (h1 _ _)
  · rintro ⟨⟨_, h1⟩, h2⟩
    refine ⟨fun v hv => ?_, fun v _ => (hK v).2 fun w _ => h1 w⟩
    obtain ⟨w0, hw0, rfl⟩ := (hF.sg _).1 hv
    exact (loc w0 hw0 (hF.pl.split w0 hw0) hv).1 (h2 w0 hw0)

private theorem elCore (hF : Fit T S VL A) {n : ℕ} (x : UA L n) (hx : x ∈ finU (E := L) (n := n))
    (O : Pl (Lp L) → Prop) (E : ∀ v, v ∈ A.Sg → GL (Fin n) (Kv v)) (d : ParN (Lp L) n)
    (hO : ∀ v, O v ↔ ∀ w, un w = v → cLoc w x = 1)
    (hE : ∀ w (_ : w ∈ S) (h : IsSplitAt w) (hv : un w ∈ A.Sg),
      cLoc w x = Matrix.GeneralLinearGroup.map ((T w h).i : Kv (un w) →+* Kw w) (E (un w) hv)) :
    ((∀ v (h : v ∈ A.Sg), E v h = Sig.dg (d v)) ∧ ∀ v ∉ A.Sg, O v) ↔
      OnS S x ∧ ∀ w ∈ S, ∀ h, cLoc w x = Sig.dg fun i => iu T w h (d (un w) i) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨hx, fun u hu => ?_⟩, fun w hw h => ?_⟩
    · have hv : un u ∉ A.Sg := fun hv => by
        obtain ⟨w, hw, e⟩ := (hF.sg _).1 hv
        exact hu w hw e.symm
      exact (hO _).1 (h2 _ hv) u rfl
    · have hv : un w ∈ A.Sg := (hF.sg _).2 ⟨w, hw, rfl⟩
      rw [hE w hw h hv, h1 _ hv]
      exact map_dg (T w h).i (d (un w))
  · rintro ⟨⟨_, h1⟩, h2⟩
    refine ⟨fun v hv => ?_, fun v hv => (hO v).2 fun w e => h1 w fun w' hw' e' => hv ?_⟩
    · obtain ⟨w0, hw0, rfl⟩ := (hF.sg _).1 hv
      have sp := hF.pl.split w0 hw0
      apply map_inj (T w0 sp).i
      rw [← hE w0 hw0 sp hv, h2 w0 hw0 sp]
      exact (map_dg (T w0 sp).i (d (un w0))).symm
    · exact (hF.sg _).2 ⟨w', hw', by rw [← e', e]⟩

private theorem expo_map {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k')
    (habs : ∀ (z : ℂ) (a : kˣ), absPow k' z (Units.map (i : k →* k') a) = absPow k z a)
    {n : ℕ} (ψ : Fin n → k'ˣ →* ℂˣ) (d : Fin n → kˣ) :
    Dict.expo ψ (fun a => Units.map (i : k →* k') (d a)) = Dict.expo (fun a => (ψ a).comp (Units.map (i : k →* k'))) d := by
  have hdet : ∀ {R : Type} [CommRing R] (t : Fin n → Rˣ) (a : Fin n),
      Matrix.GeneralLinearGroup.det ((leviTorus R (Fin n)) t a) = t a := fun t a =>
    congrFun ((leviTorus _ (Fin n)).symm_apply_apply t) a
  have h1 : torusChar ψ (fun a => Units.map (i : k →* k') (d a)) =
      torusChar (fun a => (ψ a).comp (Units.map (i : k →* k'))) d := by
    simp [torusChar_apply]
  have h2 : ((deltaHalf k' fun _ : Fin n => Unit).comp (leviTorus k' (Fin n)).toMonoidHom)
        (fun a => Units.map (i : k →* k') (d a)) =
      ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom) d := by
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, deltaHalf_apply, deltaHalf_apply]
    refine Finset.prod_congr rfl fun a _ => ?_
    have e1 := hdet (fun a => Units.map (i : k →* k') (d a)) a
    have e2 := hdet d a
    simp only [MulEquiv.coe_toMonoidHom]
    rw [e1, e2]
    exact habs _ _
  simp only [Dict.expo]
  rw [h1, h2]

end SlopeTestRemainingChoices

section Main

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {B : Bridge L} (hB : B.Ok) (T : Spl B)
  {S : Finset (Plc L)} {VL : ∀ w : Plc L, Lev (Kw w)} {A : SD B.Δ} (hF : Fit T S VL A)

include hB hF in
private theorem hsG (w : Plc L) (hw : w ∈ S) (h : IsSplitAt w) (hv : un w ∈ A.Sg) (g : GA B.Δ) :
    cLoc w (B.bG g : UA L 3) =
      Matrix.GeneralLinearGroup.map ((T w h).i : Kv (un w) →+* Kw w) (eU (A.hs _ hv) (g.1 (un w))) := by
  rw [hB.splG w (T w h) g, eU_congr (hF.s w hw h) (A.hs _ hv) (T w h).hs]

include hB hF in
private theorem hsS (w : Plc L) (hw : w ∈ S) (h : IsSplitAt w) (hv : un w ∈ A.Sg) (g : SA B.Δ) :
    cLoc w (B.bS g : UA L 2) =
      Matrix.GeneralLinearGroup.map ((T w h).i : Kv (un w) →+* Kw w) (eD (A.hs _ hv) ((g : DA B.Δ).1 (un w))) := by
  rw [hB.splS w (T w h) g, eD_congr (hF.s w hw h) (A.hs _ hv) (T w h).hs]

private theorem hfS (g : SA B.Δ) : (B.bS g : UA L 2) ∈ finU (E := L) (n := 2) := (B.bS g).2.1

include hB hF in
private theorem cl1 (hA : A.Ok) (g : GA B.Δ) : g ∈ A.dat.UG ↔ (B.bG g : UA L 3) ∈ lev (Kall (L := L) 3) S VL :=
  ((datOk _ _ A hA).2.2.2.1 g).trans (levCore T hF _ (B.bG g).2 (fun v => g.1 v ∈ KU (Ov v) _)
    (fun v h => eU (A.hs v h) (g.1 v)) (fun v => hB.KG g v) (fun w hw h hv => hsG hB T hF w hw h hv g))

include hB hF in
private theorem cl2 (hA : A.Ok) (g : SA B.Δ) :
    (g : DA B.Δ) ∈ A.dat.U2 ↔ (B.bS g : UA L 2) ∈ lev (Kall (L := L) 2) S VL :=
  ((datOk _ _ A hA).2.2.2.2 (g : DA B.Δ)).trans (levCore T hF _ (hfS g) (fun v => (g : DA B.Δ).1 v ∈ KD _ (Ov v))
    (fun v h => eD (A.hs v h) ((g : DA B.Δ).1 v)) (fun v => hB.KS g v) (fun w hw h hv => hsS hB T hF w hw h hv g))

include hB hF in
private theorem cl3 (g : GA B.Δ) (d : ParN (Lp L) 3) : A.IsElG g d ↔ OnS S (B.bG g : UA L 3) ∧
    ∀ w ∈ S, ∀ h, cLoc w (B.bG g : UA L 3) = Sig.dg fun i => iu T w h (d (un w) i) :=
  elCore T hF _ (B.bG g).2 (fun v => g.1 v = 1) (fun v h => eU (A.hs v h) (g.1 v)) d (fun v => hB.oneG g v)
    (fun w hw h hv => hsG hB T hF w hw h hv g)

include hB hF in
private theorem cl4 (g : SA B.Δ) (d : ParN (Lp L) 2) : A.IsElD g d ↔ OnS S (B.bS g : UA L 2) ∧
    ∀ w ∈ S, ∀ h, cLoc w (B.bS g : UA L 2) = Sig.dg fun i => iu T w h (d (un w) i) :=
  elCore T hF _ (hfS g) (fun v => (g : DA B.Δ).1 v = 1) (fun v h => eD (A.hs v h) ((g : DA B.Δ).1 v)) d
    (fun v => hB.oneS g v) (fun w hw h hv => hsS hB T hF w hw h hv g)

end Main

set_option maxHeartbeats 2000000 in
theorem levG : LevG := by
  intro L _ _ _ B hB T S VL A hA hF
  refine ⟨?_, ?_, ?_, ?_, fun w h n ψ d _ => expo_map (T w h).i (T w h).abs ψ d⟩
  · with_reducible exact cl1 hB T hF hA
  · with_reducible exact cl2 hB T hF hA
  · with_reducible exact cl3 hB T hF
  · with_reducible exact cl4 hB T hF

end UpperTheory.V.Z.Sym.So

end
end

