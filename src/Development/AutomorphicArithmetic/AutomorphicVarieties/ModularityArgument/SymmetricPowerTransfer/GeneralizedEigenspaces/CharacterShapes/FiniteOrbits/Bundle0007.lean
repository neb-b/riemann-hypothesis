module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.KirillovFunctionValueEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.LocalLevelOutsideSigma
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IndexNeZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.OutOrbit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.UnitaryThreeTestFunctionHeckeRelations
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.DiagonalParameterDominant
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

section Scalar

variable {k : Type} [Field k]

private theorem dg_comm (z : kˣ) (x : GL (Fin 2) k) : dg ![z, z] * x = x * dg ![z, z] := by
  have h : (fun i => ((![z, z] i : kˣ) : k)) = fun _ => (z : k) := by
    funext i
    fin_cases i <;> rfl
  apply Units.ext
  simp only [Units.val_mul, val_diagT, h]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

end Scalar

variable {F : Type} [Field F] [NumberField F] {Δ : F} (A : SD Δ)

private abbrev d1 (t : Dat.Par F) : ParN F 2 := fun v => ![t v, 1]

private theorem diagonal_parameter_mul (t t' : Dat.Par F) : d1 (t * t') = d1 t * d1 t' := by
  funext v i
  fin_cases i <;> simp [d1]

private theorem diagonal_parameter_dominant {t : Dat.Par F} (h : ∀ v ∈ A.Sg, valuation (Kv v) (t v : Kv v) ≤ 1) : A.DomS (d1 t) := by
  intro v hv i j hij
  fin_cases i <;> fin_cases j
  · exact le_rfl
  · simpa using h v hv
  · exact absurd hij (by decide)
  · exact le_rfl

private theorem cone_le {t : Dat.Par F} (h : A.Cone t) : ∀ v ∈ A.Sg, valuation (Kv v) (t v : Kv v) ≤ 1 := by
  intro v hv
  refine (h v hv).le.trans (pow_le_one₀ zero_le' ?_)
  rw [GlAx.unif_spec]
  exact uniformizer_lt_one.le

private theorem cone_mul {x y : Dat.Par F} (hx : ∀ v ∈ A.Sg, valuation (Kv v) (x v : Kv v) ≤ 1) (hy : A.Cone y) :
    A.Cone (x * y) := by
  intro v hv
  have h : valuation (Kv v) ((x * y) v : Kv v) = valuation (Kv v) (x v : Kv v) * valuation (Kv v) (y v : Kv v) := by
    rw [Pi.mul_apply, Units.val_mul, map_mul]
  rw [h]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' (hx v hv)) (hy v hv)

private def cc (t : Dat.Par F) : ℂ := ∏ v ∈ A.Sg, (((A.χ v (t v))⁻¹ : ℂˣ) : ℂ)

private def pp (a : Chs F) (t : Dat.Par F) : ℂ := ∏ v ∈ A.Sg, ((a v (t v) : ℂˣ) : ℂ)

private theorem cc_mul (t t' : Dat.Par F) : cc A (t * t') = cc A t * cc A t' := by
  simp only [cc, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Pi.mul_apply, map_mul, mul_inv, Units.val_mul]

private theorem pp_mul (a : Chs F) (t t' : Dat.Par F) : pp A a (t * t') = pp A a t * pp A a t' := by
  simp only [pp, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Pi.mul_apply, map_mul, Units.val_mul]

private theorem cc_ne (t : Dat.Par F) : cc A t ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ _ => Units.ne_zero _

private theorem pp_ne (a : Chs F) (t : Dat.Par F) : pp A a t ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ _ => Units.ne_zero _

private theorem pp_sq (a : Chs F) (t : Dat.Par F) : pp A (a ^ 2) t = pp A a (t * t) := by
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Pi.pow_apply, MonoidHom.pow_apply, Pi.mul_apply, map_mul, pow_two]

private theorem exS_eq (hA : A.Ok) (a : Chs F) (t : Dat.Par F) : A.exS a t = pp A a t * cc A t := by
  simp only [SD.exS, pp, cc, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v hv => ?_
  have hχ : A.χ v = absPow (Kv v) 1 := ((datOk F Δ A hA).2.2.1 v hv).2.2.2.2
  have h := (expoEq (Kv v) (a v)).2.1 (t v)
  rw [SD.dS, h, hχ, absPow_neg, MonoidHom.inv_apply]

private theorem conj_mem (hA : A.Ok) {s u : DA Δ} {z : Dat.Par F} (hs : A.IsElD s fun v => ![z v, z v])
    (hu : u ∈ A.dat.U2) : s⁻¹ * u * s ∈ A.dat.U2 := by
  have hU := (datOk F Δ A hA).2.2.2.2
  rw [hU] at hu ⊢
  refine ⟨fun v h => ?_, fun v h => ?_⟩
  · have e : (s⁻¹ * u * s).1 v = (s.1 v)⁻¹ * u.1 v * s.1 v := rfl
    have e' : eD (A.hs v h) (s.1 v) = dg ![z v, z v] := hs.1 v h
    rw [e, map_mul, map_mul, map_inv, e', mul_assoc, ← dg_comm, inv_mul_cancel_left]
    exact hu.1 v h
  · have e : (s⁻¹ * u * s).1 v = (s.1 v)⁻¹ * u.1 v * s.1 v := rfl
    rw [e, hs.2 v h]
    simpa using hu.2 v h

variable {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem dc_smul {G : Type} [Group G] (U : Subgroup G) (a : G) (c : ℂ) (φ : G → V) :
    dcF U a (c • φ) = c • dcF U a φ :=
  map_smul (dc (rightReg ℂ G V) U U a) c φ

private theorem mulOp (hA : A.Ok) {g g' : DA Δ} {d d' : ParN F 2} (hg : A.IsElD g d) (hg' : A.IsElD g' d')
    (hd : A.DomS d) (hd' : A.DomS d') (φ : DA Δ → V) (hφ : ∀ u ∈ A.dat.U2, ∀ x, φ (x * u) = φ x) :
    dcF A.dat.U2 (g * g') φ = dcF A.dat.U2 g (dcF A.dat.U2 g' φ) := by
  have hm := (elEx F Δ A hA).2.2.2.1 g g' d d' hg hg'
  exact (uFMul _ V _ g g' (dMul F Δ A hA g d hg).1 (dMul F Δ A hA g' d' hg').1 (dMul F Δ A hA _ _ hm).1
    ((dMul F Δ A hA g d hg).2 g' d' hg' hd hd') φ hφ).symm

private theorem dcScal (hA : A.Ok) {s : DA Δ} {z : Dat.Par F} (hs : A.IsElD s fun v => ![z v, z v])
    (φ : DA Δ → V) (hφ : ∀ u ∈ A.dat.U2, ∀ x, φ (x * u) = φ x) (x : DA Δ) :
    dcF A.dat.U2 s φ x = φ (x * s) := by
  have h1 : ∀ y ∈ ({s} : Finset (DA Δ)), y ∈ DC A.dat.U2 s := by
    intro y hy
    rw [Finset.mem_singleton] at hy
    subst hy
    exact ⟨1, one_mem _, 1, one_mem _, by simp⟩
  have h2 : ∀ y ∈ DC A.dat.U2 s, ∃! r, r ∈ ({s} : Finset (DA Δ)) ∧ r⁻¹ * y ∈ A.dat.U2 := by
    rintro y ⟨u, hu, u', hu', rfl⟩
    refine ⟨s, ⟨Finset.mem_singleton_self _, ?_⟩, fun r hr => Finset.mem_singleton.1 hr.1⟩
    have e : s⁻¹ * (u * s * u') = (s⁻¹ * u * s) * u' := by group
    rw [e]
    exact mul_mem (conj_mem A hA hs hu) hu'
  have h := (dcBasic _ V A.dat.U2 s (dMul F Δ A hA s _ hs).1 φ hφ).2.2.2.2 {s} h1 h2 x
  simpa using h

end UpperTheory.V.Z.Sym.So

theorem UpperTheory.V.Z.Sym.So.kSpec :
    UpperTheory.V.Z.Sym.So.KSpec := by
  intro F _ _ Δ A hA V _ _ ch B hB
  obtain ⟨hop, hinv, hsc⟩ := kOps F Δ A hA V ch B hB
  have hexD := (elEx F Δ A hA).2.1
  have hmulD := (elEx F Δ A hA).2.2.2.1
  refine ⟨?_, ?_⟩
  · intro t t' ht ht'
    refine LinearMap.ext fun φ => Subtype.ext ?_
    obtain ⟨g, hg, -⟩ := hexD (d1 t)
    obtain ⟨g', hg', -⟩ := hexD (d1 t')
    have hgg : A.IsElD (g * g') (d1 (t * t')) := by
      rw [diagonal_parameter_mul]
      exact hmulD _ _ _ _ hg hg'
    have e1 := hop (t * t') (g * g') (cone_mul A (cone_le A ht) ht') hgg φ
    have e2 := hop t g ht hg ((Base.Tw.one B).R (A.dat.FK t') φ)
    have e3 := hop t' g' ht' hg' φ
    rw [Module.End.mul_apply, e1, e2, e3, dc_smul, smul_smul,
      mulOp A hA hg hg' (diagonal_parameter_dominant A (cone_le A ht)) (diagonal_parameter_dominant A (cone_le A ht')) φ.1 (hinv φ.1 φ.2)]
    have := cc_mul A t t'
    simp only [cc] at this
    rw [this]
  · intro a φ hE t g hd hg
    have hφ := hinv φ.1 φ.2
    have hT : ∀ τ h, A.Cone τ → A.IsElD h (d1 τ) → dcF A.dat.U2 h φ.1 = pp A a τ • φ.1 := by
      intro τ h hτ hh
      have h1 := congrArg Subtype.val (hE τ hτ)
      rw [hop τ h hτ hh φ, Submodule.coe_smul, exS_eq A hA, mul_comm, ← smul_smul] at h1
      exact smul_right_injective _ (cc_ne A τ) h1
    have ht2 : ∀ v ∈ A.Sg, valuation (Kv v) ((t * t) v : Kv v) ≤ 1 := by
      intro v hv
      have h0 : valuation (Kv v) (t v : Kv v) ≤ valuation (Kv v) (((t v)⁻¹ : (Kv v)ˣ) : Kv v) := by
        simpa [SD.dS] using hd v hv 0 1 (by decide)
      have h1 := mul_le_mul' h0 (le_refl (valuation (Kv v) (t v : Kv v)))
      have e : valuation (Kv v) (((t v)⁻¹ : (Kv v)ˣ) : Kv v) * valuation (Kv v) (t v : Kv v) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      rw [e, ← map_mul] at h1
      rw [Pi.mul_apply, Units.val_mul]
      exact h1
    let t0 : Dat.Par F := fun v => unif (Kv v) ^ 3
    have h0 : A.Cone t0 := by
      intro v hv
      show valuation (Kv v) ((unif (Kv v) ^ 3 : (Kv v)ˣ) : Kv v) < _
      rw [Units.val_pow_eq_pow_val, map_pow, GlAx.unif_spec]
      exact pow_lt_pow_right_of_lt_one₀ uniformizer_pos uniformizer_lt_one (by norm_num)
    obtain ⟨g0, hg0, -⟩ := hexD (d1 t0)
    obtain ⟨g1, hg1, -⟩ := hexD (d1 (t * t))
    have hgg : A.IsElD (g1 * g0) (d1 (t * t * t0)) := by
      rw [diagonal_parameter_mul]
      exact hmulD _ _ _ _ hg1 hg0
    have hg1φ : dcF A.dat.U2 g1 φ.1 = pp A a (t * t) • φ.1 := by
      have e := hT _ _ (cone_mul A ht2 h0) hgg
      rw [mulOp A hA hg1 hg0 (diagonal_parameter_dominant A ht2) (diagonal_parameter_dominant A (cone_le A h0)) φ.1 hφ, hT _ _ h0 hg0, dc_smul, pp_mul,
        mul_comm, ← smul_smul] at e
      exact smul_right_injective _ (pp_ne A a t0) e
    obtain ⟨s, hs, -⟩ := hexD fun v => ![t⁻¹ v, t⁻¹ v]
    have hm : A.IsElD (g1 * s) (SD.dS t) := by
      have e : SD.dS t = d1 (t * t) * fun v => ![t⁻¹ v, t⁻¹ v] := by
        funext v i
        fin_cases i <;> simp [SD.dS]
      rw [e]
      exact hmulD _ _ _ _ hg1 hs
    have hgs : g = g1 * s := (hexD (SD.dS t)).unique hg hm
    have hdom : A.DomS fun v => ![t⁻¹ v, t⁻¹ v] := by
      intro v _ i j _
      fin_cases i <;> fin_cases j <;> exact le_rfl
    have hsφ : dcF A.dat.U2 s φ.1 = cc A t • φ.1 := by
      funext x
      rw [dcScal A hA hs φ.1 hφ x, hsc φ.1 φ.2 _ s hs x, Pi.smul_apply]
      congr 1
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [Pi.inv_apply, map_inv]
    rw [hgs, mulOp A hA hg1 hs (diagonal_parameter_dominant A ht2) hdom φ.1 hφ, hsφ, dc_smul, hg1φ, smul_smul, exS_eq A hA, pp_sq,
      mul_comm]

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.GOpsEx
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem uf_dg (V : Lev k) (d d' : Fin 3 → kˣ) (hd : Dom d) (hd' : Dom d') :
    UF (V.J 3) (dg d) (dg d') := by
  intro g
  have h := dCMul k V 3 d d' hd hd' g
  have hm : dg (d * d') = dg d * dg d' := map_mul _ _ _
  simp only [Lev.DC, hm] at h
  exact h

private theorem dg_mem (V : Lev k) (d : Fin 3 → kˣ) (hd : ∀ i, d i ∈ V.H) : dg d ∈ V.J 3 := by
  refine Subgroup.mem_sup_left (Subgroup.mem_sup_right ?_)
  exact ⟨d, by simpa [Subgroup.mem_pi] using hd, rfl⟩

end Local

variable {F : Type} [Field F] [NumberField F] {Δ : F}

private theorem jv_in (A : SD Δ) {v : Pl F} (h : v ∈ A.Sg) :
    A.dat.Jv v = ((A.V v).J 3).comap (eU (A.hs v h)) := by
  simp [Dat.Jv, SD.dat, h, Lev.data]

private theorem jv_off (A : SD Δ) {v : Pl F} (h : v ∉ A.Sg) : A.dat.Jv v = KU (Ov v) _ := if_neg h

private theorem eU_bij (A : SD Δ) (hA : A.Ok) {v : Pl F} (h : v ∈ A.Sg) :
    Function.Bijective (eU (A.hs v h)) := by
  obtain ⟨h1, h2, h3, -⟩ := (datOk F Δ A hA).2.2.1 v h
  exact (eU_facts (Kv v) (Ov v) h1 h2 (cv v Δ) (A.s v) (A.hs v h) h3).1

private theorem finOrb_G (A : SD Δ) (hA : A.Ok) (g : GA Δ) (d : ParN F 3) (hg : A.IsElG g d) :
    AlgebraTools.FinOrb A.dat.UG A.dat.UG g := by
  classical
  let P := rpg (fun v => U3 ((cv v) Δ)) (fun v => KU (Ov v) ((cv v) Δ))
  have hpv : ∀ (x : GA Δ) v, P.p v x = (x : (v : Pl F) → U3 ((cv v) Δ)) v := fun _ _ => rfl
  have hout : ∀ v ∉ A.Sg, P.p v g ∈ A.dat.Jv v := by
    intro v hv
    rw [jv_off A hv, hpv, hg.2 v hv]
    exact one_mem _
  have hbox := uFBox (Pl F) (GA Δ) (fun v => U3 ((cv v) Δ)) (fun v => KU (Ov v) ((cv v) Δ))
    A.dat.Jv P A.Sg (fun v hv => jv_off A hv) g hout
  refine hbox.2.1 (fun v hv => ?_)
  rw [jv_in A hv]
  have dm := dcMap _ _ ℂ (eU (A.hs v hv)) (eU_bij A hA hv) ((A.V v).J 3) (P.p v g) (P.p v g)
  rw [dm.2.1, hpv, hg.1 v hv]
  exact ((finFacts (Kv v) (A.V v)).2.2.2.2.2 3).1 _

private theorem uf_G (A : SD Δ) (hA : A.Ok) (g g' : GA Δ) (d d' : ParN F 3) (hg : A.IsElG g d)
    (hg' : A.IsElG g' d') (hd : A.DomS d) (hd' : A.DomS d') : UF A.dat.UG g g' := by
  classical
  let P := rpg (fun v => U3 ((cv v) Δ)) (fun v => KU (Ov v) ((cv v) Δ))
  have hpv : ∀ (x : GA Δ) v, P.p v x = (x : (v : Pl F) → U3 ((cv v) Δ)) v := fun _ _ => rfl
  have hout : ∀ (x : GA Δ) (e : ParN F 3), A.IsElG x e → ∀ v ∉ A.Sg, P.p v x ∈ A.dat.Jv v := by
    intro x e hx v hv
    rw [jv_off A hv, hpv, hx.2 v hv]
    exact one_mem _
  have hbox := uFBox (Pl F) (GA Δ) (fun v => U3 ((cv v) Δ)) (fun v => KU (Ov v) ((cv v) Δ))
    A.dat.Jv P A.Sg (fun v hv => jv_off A hv) g (hout g d hg)
  refine hbox.2.2 g' (hout g' d' hg') (fun v hv => ?_)
  rw [jv_in A hv]
  have dm := dcMap _ _ ℂ (eU (A.hs v hv)) (eU_bij A hA hv) ((A.V v).J 3) (P.p v g) (P.p v g')
  rw [dm.2.2.1, hpv, hpv, hg.1 v hv, hg'.1 v hv]
  exact uf_dg (A.V v) (d v) (d' v) (hd v hv) (hd' v hv)

end UpperTheory.V.Z.Sym.So

theorem UpperTheory.V.Z.Sym.So.gOpsEx :
    UpperTheory.V.Z.Sym.So.GOpsEx := by
  intro F _ _ Δ A hA V _ _ ch B s hB
  classical
  obtain ⟨hG, -, hmul, -, -⟩ := elEx F Δ A hA
  have hF := hecke_operators_on_twisted_base_function F Δ A hA V ch B s hB
  let gd : ParN F 3 → GA Δ := fun d => (hG d).exists.choose
  have hgd : ∀ d, A.IsElG (gd d) d := fun d => (hG d).exists.choose_spec
  have huniq : ∀ d g, A.IsElG g d → g = gd d := fun d g h => (hG d).unique h (hgd d)
  let u : ParN F 3 → Module.End ℂ ↥B.Forms :=
    fun d => (Base.Tw.one B).R fun y => one (y ∈ DC B.U (gd d))
  have hω := hB.ω
  have hU := hB.U
  have hfin : ∀ d, AlgebraTools.FinOrb A.dat.UG A.dat.UG (gd d) := fun d => finOrb_G A hA _ d (hgd d)
  have hop : ∀ d, ∀ φ : ↥B.Forms, ((u d φ : ↥B.Forms) : GA Δ → V) = dcF A.dat.UG (gd d) φ := by
    intro d φ
    have h := (opDc _ _ _ B hω (gd d) (by rw [hU]; exact hfin d)).2 φ
    exact h.trans (by rw [hU])
  have hinv : ∀ φ : ↥B.Forms, ∀ x ∈ A.dat.UG, ∀ g,
      (φ : GA Δ → V) (g * x) = (φ : GA Δ → V) g := by
    intro φ x hx g
    have h := φ.2.2 g ⟨x, by rw [hU]; exact hx⟩
    rw [hω] at h
    simpa using h
  refine ⟨u, s.R (A.F0 1), ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro d g hd hg φ
    rw [huniq d g hg]
    exact hop d φ
  · intro d d' hd hd'
    have he : gd (d * d') = gd d * gd d' := (huniq _ _ (hmul _ _ _ _ (hgd d) (hgd d'))).symm
    apply LinearMap.ext
    intro φ
    apply Subtype.ext
    simp only [Module.End.mul_apply, hop]
    rw [he]
    exact (uFMul _ V A.dat.UG (gd d) (gd d') (hfin d) (hfin d') (by rw [← he]; exact hfin _)
      (uf_G A hA _ _ d d' (hgd d) (hgd d') hd hd') (φ : GA Δ → V) (hinv φ)).symm
  · intro d hd
    have hmem : gd d ∈ A.dat.UG := by
      show gd d ∈ (rpg (fun v => U3 ((cv v) Δ)) (fun v => KU (Ov v) ((cv v) Δ))).box A.dat.Jv
      simp only [RPG.box, Subgroup.mem_iInf, Subgroup.mem_comap]
      intro v
      by_cases hv : v ∈ A.Sg
      · rw [jv_in A hv, Subgroup.mem_comap]
        show eU (A.hs v hv) ((gd d : (v : Pl F) → U3 ((cv v) Δ)) v) ∈ _
        rw [(hgd d).1 v hv]
        exact dg_mem (A.V v) (d v) (hd v hv)
      · rw [jv_off A hv]
        show ((gd d : (v : Pl F) → U3 ((cv v) Δ)) v) ∈ _
        rw [(hgd d).2 v hv]
        exact one_mem _
    apply LinearMap.ext
    intro φ
    apply Subtype.ext
    rw [hop, (dcBasic _ V A.dat.UG (gd d) (hfin d) (φ : GA Δ → V) (hinv φ)).2.2.2.1 hmem]
    rfl
  · intro d hd
    have f1 := ((hF.1 (SD.sg d) (gd (SD.sg d)) (hgd _))).2.1
    have f2 := ((hF.1 d (gd d) (hgd d))).2.2
    exact f2.symm.trans f1
  · intro t ht
    rw [hF.2 t ht]
    have hl := Tf.rLin _ _ _ B s _ A.Ys (fun _ => 1) (fun y => A.F0 (A.dG t y))
      (fun y _ => (hF.1 _ _ (hgd _)).1)
    simp only [one_mul, one_smul] at hl
    rw [hl.2]
    exact Finset.sum_congr rfl fun y _ => (hF.1 _ _ (hgd _)).2.1

end
end

