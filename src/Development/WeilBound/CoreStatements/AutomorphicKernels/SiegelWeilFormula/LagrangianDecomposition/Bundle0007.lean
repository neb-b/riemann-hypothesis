module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1703
public import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.ResAdm
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ChartB
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

set_option linter.unusedSectionVars false

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem trace_mul_single' {m k : ℕ} (A : Matrix (Fin k) (Fin m) (AE F E)) (a : Fin m) (c : Fin k) (z : AE F E) :
    (A * Matrix.single a c z).trace = A c a * z := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and]

theorem map_single' {m k : ℕ} (a : Fin m) (c : Fin k) (z : AE F E) :
    (Matrix.single a c z).map (cA σ) = Matrix.single a c (cA σ z) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem Bf_Ek {m k : ℕ} (bs : Module.Basis (Fin 2) F E) (J : Matrix (Fin m) (Fin m) E) (X : Mx F E m k)
    (q : Fin m × Fin k × Fin 2) : Bf σ J X (Ek bs q) =
      Algebra.trace (AF F) (AE F E) ((∑ p, X p q.2.1 * incM F J p q.1) * cA σ ((1 : AF F) ⊗ₜ[F] bs q.2.2)) := by
  unfold Bf Ek
  rw [map_single', trace_mul_single']
  simp [Matrix.mul_apply, Matrix.transpose_apply]

theorem Bf_col {m k k' : ℕ} (bs : Module.Basis (Fin 2) F E) (J : Matrix (Fin m) (Fin m) E) (X : Mx F E m k)
    (X' : Mx F E m k') (a : Fin m) (c : Fin k) (c' : Fin k') (t : Fin 2) (hX : ∀ p, X p c = X' p c') :
    Bf σ J X (Ek bs (a, c, t)) = Bf σ J X' (Ek bs (a, c', t)) := by
  simp only [Bf_Ek, hX]

theorem Bf_zero_col {m k : ℕ} (bs : Module.Basis (Fin 2) F E) (J : Matrix (Fin m) (Fin m) E) (X : Mx F E m k)
    (a : Fin m) (c : Fin k) (t : Fin 2) (hX : ∀ p, X p c = 0) : Bf σ J X (Ek bs (a, c, t)) = 0 := by
  rw [Bf_Ek]
  simp [hX]

theorem crdB_col {m k k' : ℕ} (bs : Module.Basis (Fin 2) F E) (X : Mx F E m k) (X' : Mx F E m k') (a : Fin m)
    (c : Fin k) (c' : Fin k') (t : Fin 2) (hX : X a c = X' a c') : crdB bs X (a, c, t) = crdB bs X' (a, c', t) := by
  simp only [crdB, hX]

theorem crdB_zero_col {m k : ℕ} (bs : Module.Basis (Fin 2) F E) (X : Mx F E m k) (a : Fin m) (c : Fin k) (t : Fin 2)
    (hX : X a c = 0) : crdB bs X (a, c, t) = 0 := by
  simp [crdB, hX]

theorem extend_zero_embedded_column {m n N : ℕ} (h : n + 1 = N) (X : Mx F E m n) (p : Fin m) (j : Fin n) : ext0 h X p (em0 h j) = X p j := by
  simp [ext0, em0]

theorem extend_zero_last_column {m n N : ℕ} (h : n + 1 = N) (X : Mx F E m n) (p : Fin m) : ext0 h X p (i0 h) = 0 := by
  simp [ext0, i0]

end PositivityTheory.SiegelWeilFormula.Ald

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ModelPf
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem Bf_zero_left {m n : ℕ} (J : Matrix (Fin m) (Fin m) E) (Z : Mx F E m n) : Bf σ J 0 Z = 0 := by
  simp [Bf]

theorem tof_adapted {m n : ℕ} {A : Spc F E m} {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} (bs : Module.Basis (Fin 2) F E)
    (ψ : AddChar (AF F) ℂ)
    {dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) (Fin m × Fin n × Fin 2)}
    (had : IsAdapted bs A Y b dd) (Φ : (Fin m × Fin n × Fin 2 → AF F) → ℂ) (X : Mx F E m n) :
    Tof ψ dd (ev0 _) b Φ X = Φ (crdB bs X) := by
  have e := had 0 X
  rw [Matrix.zero_mul, zero_add] at e
  change dd.e (X * (b.1.toCols₂.map (inclR (AF F)))ᵀ) = _ at e
  simp only [Tof, ev0, LinearMap.coe_mk, AddHom.coe_mk, Darboux.rho, schr, e, Bf_zero_left]
  simp

theorem crdB_eK {m n N : ℕ} (h : n + 1 = N) (bs : Module.Basis (Fin 2) F E) (X : Mx F E m N)
    (hX : ∀ a, X a (i0 h) = 0) :
    crdB bs X ∘ eK m h = Sum.elim (crdB bs (X.submatrix id (em0 h))) 0 := by
  funext k
  rcases k with ⟨a, i, t⟩ | ⟨a, t⟩
  · rfl
  · simp [crdB, eK, hX]

theorem crdB_surj {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (x : Fin m × Fin n × Fin 2 → AF F) :
    ∃ X : Mx F E m n, crdB bs X = x := by
  refine ⟨fun a i => (Algebra.TensorProduct.basis (AF F) bs).repr.symm (Finsupp.equivFunOnFinite.symm fun t => x (a, i, t)),
    funext fun k => ?_⟩
  simp [crdB]

theorem extend_zero_column {m n N : ℕ} (h : n + 1 = N) (X : Mx F E m n) : ∀ a, ext0 h X a (i0 h) = 0 := fun a => by
  simp [ext0, i0]

theorem extension_zero_sub {m n N : ℕ} (h : n + 1 = N) (X : Mx F E m n) : (ext0 h X).submatrix id (em0 h) = X := by
  funext a i
  simp [ext0, em0]

theorem modelEx_of (hS : SDarb) (hE : SEv) (hB : BigT) (hF : SliceFacts) (hO : OpBox) (hU : SubSplit)
    (hC : ChartFacts) (hG : SiegelSmall) (hA' : SmallS) : ModelEx := by
  intro hT hA F E _ _ _ _ _ σ d n h Y b j hn hs hb hε hj
  obtain ⟨ε, e1, e2⟩ := hε
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨dd0, had0, hr0⟩ := hS F E σ d.B d.bs d.m d.n d.A d.Y d.b ε d.r d.s d.ok.good d.ok.hm d.ok.hn d.ok.sign
    d.ok.frame e1
  obtain ⟨dd', had', hr'⟩ := hS F E σ d.B d.bs d.m n d.A Y b ε d.r d.s d.ok.good d.ok.hm hn hs hb e2
  obtain ⟨hev, hkill, htheta⟩ := hE F E σ d.B d.bs d.m n d.A Y b ε d.r d.s d.ok.good d.ok.hm hn hs hb e2 dd' had'
  obtain ⟨S0, S0', C, hC0, hop, hTf⟩ := hB hT hA F E σ d dd0 had0 hr0
  obtain ⟨c1, c2, c3, c4, -⟩ := hC F E σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had'

  let dd1 := GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm
  let S1 := GlobalTheory.TowU.RealComp.reix (eK d.m h) ∘ₗ S0
  let S1' := S0' ∘ₗ GlobalTheory.TowU.RealComp.reix (eK d.m h).symm
  have hop1 : GlobalTheory.TowU.IsOp d.B.ψ (fun w => dd1.e (d.dd.e.symm w)) S1 S1' :=
    GlobalTheory.TowU.RealComp.isOp_comp hop.1 (GlobalTheory.TowU.RealComp.isOp_reix d.B.ψ (eK d.m h))
  have hT1 : ∀ Φ ∈ d.sch, ∀ X, d.T Φ X = C * S1 Φ (crdB d.bs X ∘ eK d.m h) := fun Φ hΦ X => by
    rw [hTf Φ hΦ X]
    simp only [S1, LinearMap.comp_apply, GlobalTheory.TowU.RealComp.reix_apply]
    rw [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
  have hw := d.ok.dbl.weil
  obtain ⟨om1, hom1⟩ := projHom (G := d.G) (fun x => S1 ∘ₗ d.om x ∘ₗ S1')
    (fun x φ hφ => hop1.pres _ (hw.2.1.pres x _ (hop1.pres' φ hφ)))
    (fun φ hφ => by simp [hop1.right φ hφ])
    (fun x y φ hφ => by
      simp only [LinearMap.comp_apply, map_mul, Module.End.mul_apply]
      rw [hop1.left _ (hw.2.1.pres y _ (hop1.pres' φ hφ))])
  have hsp1 : IsUSplitting (adeleClass F) d.B.ψ dd1 (actB (cA σ)) om1 :=
    GlobalTheory.TowU.isUSplitting_of_isOp hψ (fun w => by simp) hop1 hom1 hw.2.1
  have hsr1 : SiegelRule (cA σ) (adeleClass F) d.B.ψ (-1) (incM F d.A.J) (dbl (incM F d.Y.J)) dd1 d.χ
      (diagCols (Fin d.n)) om1 :=
    GlobalTheory.TowU.siegelRule_of_isOp (fun w => by simp) hop1 hom1 hw.2.2

  obtain ⟨hsl1, hsl2, ⟨φ₀, hφ₀, hφ₀0, hφ₀n⟩, -⟩ := hF F (Fin d.m × Fin n × Fin 2) (Fin d.m × Fin 2)
  have hbox := fun g => hO F d.B.ψ hψ _ _ _ _ dd1 d.G (actB (cA σ)) om1 hsp1.toIsSplitting c2 (j g) (c3 g) φ₀ hφ₀ hφ₀0

  let cg : G2 σ Y → ((Fin d.m × Fin n × Fin 2 → AF F) → ℂ) →ₗ[ℂ] ((Fin d.m × Fin n × Fin 2 → AF F) → ℂ) :=
    fun g => slice0 _ _ ∘ₗ om1 (j g) ∘ₗ PositivityTheory.ThKF0.Chr.boxL _ φ₀
  have hbx : ∀ φ' ∈ schA F (Fin d.m × Fin n × Fin 2), boxFun φ' φ₀ ∈ schA F (K1 d.m n) := fun φ' hφ' =>
    GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ' hφ' φ₀ hφ₀
  have hsl0 : ∀ φ' : (Fin d.m × Fin n × Fin 2 → AF F) → ℂ, slice0 _ _ (boxFun φ' φ₀) = φ' := fun φ' => by
    funext x
    simp [slice0, boxFun, hφ₀0]
  have hcg : ∀ g φ', cg g φ' = slice0 _ _ (om1 (j g) (boxFun φ' φ₀)) := fun g φ' => rfl
  have hboxc : ∀ g, ∀ φ' ∈ schA F (Fin d.m × Fin n × Fin 2),
      om1 (j g) (boxFun φ' φ₀) = boxFun (cg g φ') φ₀ := fun g φ' hφ' =>
    (hbox g).2 φ' hφ' φ₀ hφ₀
  obtain ⟨om', hom'⟩ := projHom cg
    (fun g φ' hφ' => hsl1 _ (hsp1.pres _ _ (hbx φ' hφ')))
    (fun φ' hφ' => by rw [hcg, map_one, map_one, Module.End.one_apply, hsl0])
    (fun g g' φ' hφ' => by
      rw [hcg, map_mul, map_mul, Module.End.mul_apply, hboxc g' φ' hφ', hcg g])
  have hboxom : ∀ g, ∀ φ' ∈ schA F (Fin d.m × Fin n × Fin 2), om1 (j g) (boxFun φ' φ₀) = boxFun (om' g φ') φ₀ :=
    fun g φ' hφ' => by rw [hom' g φ' hφ', hboxc g φ' hφ']
  have hsp' : IsUSplitting (adeleClass F) d.B.ψ dd' (actB (cA σ)) om' :=
    hU F d.B.ψ hψ _ _ _ _ _ _ dd1 dd' (emb h b d.b) c1 d.G (G2 σ Y) (actB (cA σ)) (actB (cA σ)) j hj.1 c4 om1 om' hsp1
      φ₀ hφ₀ hφ₀0 hφ₀n (fun g => ⟨φ₀, hφ₀, hφ₀0, fun _ _ => rfl, hboxom g⟩)
  have hsg' := hG F E σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had' om1 hsp1.toIsSplitting hsr1 φ₀ hφ₀ hφ₀0 om'
    hboxom
  obtain ⟨S', hS'1, hS'2⟩ := hA' hT F E σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had' S1 S1' C hC0 hop1 hT1
  refine ⟨Fin d.m × Fin n × Fin 2, inferInstance, dd', om', S', ev0 _,
    ⟨hr', ⟨isLagr_diagCols _ _, hsp', hsg'⟩, hS'1, hev, hkill, hS'2, htheta⟩, ?_⟩

  intro Φ hΦ Φ' hΦ' hres g X hX
  have hS1Φ : S1 Φ ∈ schA F (K1 d.m n) := hop1.pres Φ hΦ
  have hsl : Φ' = C • slice0 _ _ (S1 Φ) := by
    funext x
    obtain ⟨X', rfl⟩ := crdB_surj d.bs x
    have e := hres (ext0 h X') (extend_zero_column h X')
    rw [extension_zero_sub, tof_adapted d.bs d.B.ψ had', hT1 Φ hΦ, crdB_eK h d.bs _ (extend_zero_column h X'), extension_zero_sub] at e
    rw [e]
    rfl
  rw [tof_adapted d.bs d.B.ψ had', hom' g Φ' hΦ', hT1 _ (hw.2.1.pres (j g) Φ hΦ), crdB_eK h d.bs X hX]
  have e1' : S1 (d.om (j g) Φ) = om1 (j g) (S1 Φ) := by
    rw [hom1 (j g) _ hS1Φ]
    simp only [LinearMap.comp_apply]
    rw [hop1.left Φ hΦ]
  rw [e1', show (Sum.elim (crdB d.bs (X.submatrix id (em0 h))) 0 : K1 d.m n → AF F) =
    Sum.elim (crdB d.bs (X.submatrix id (em0 h))) 0 from rfl]
  have e2' := congrFun ((hbox g).1 (S1 Φ) hS1Φ) (crdB d.bs (X.submatrix id (em0 h)))
  simp only [slice0, LinearMap.coe_mk, AddHom.coe_mk] at e2'
  rw [e2', hcg, hsl]
  simp only [slice0, LinearMap.coe_mk, AddHom.coe_mk]
  rw [GlobalTheory.SchwartzBox.boxFun_smul_left, map_smul]
  rfl

end PositivityTheory.SiegelWeilFormula.Ald

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SiegelB
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

set_option linter.unusedSectionVars false

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem incM_mul {ι κ ν : Type} [Fintype κ] (M : Matrix ι κ E) (N : Matrix κ ν E) :
    incM F (M * N) = incM F M * incM F N := by
  simp only [incM]
  exact Matrix.map_mul (f := (inclR (F := F) (E := E) (AF F)))

theorem incM_diagCols (n : ℕ) :
    incM F (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E) = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) := by
  ext u k
  rcases u with u | u <;> simp [incM, diagCols, Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all

theorem mul_fromRows_one_zero {R : Type*} [CommRing R] {n : ℕ} (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    M * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (0 : Matrix (Fin n) (Fin n) R) = M.toCols₁ := by
  ext u k
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toCols₁]

theorem frame_fromRows {n : ℕ} {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} (hb : IsFrame2 σ Y b) :
    ∃ tb : GL (Fin n) E, incM F b.1 * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (0 : Matrix (Fin n) (Fin n) (AE F E)) =
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * incM F tb.1 := by
  obtain ⟨-, tb, htb0⟩ := hb
  have htb : b.1.toCols₁ = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E) * tb.1 := htb0
  refine ⟨tb, ?_⟩
  have e : (incM F b.1).toCols₁ = incM F b.1.toCols₁ := rfl
  rw [mul_fromRows_one_zero, e, htb, incM_mul]
  congr 1
  ext u k
  rcases u with u | u <;> simp [incM, diagCols, Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all

theorem frame_decomp {m n : ℕ} (b : GL (Fin n ⊕ Fin n) E) (w : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) :
    w = (frQ b w).toCols₁ * (incM F b.1.toCols₁)ᵀ + (frQ b w).toCols₂ * (incM F b.1.toCols₂)ᵀ := by
  have e1 : frQ b w * (incM F b.1)ᵀ = w := by
    change (w * (incM F (b⁻¹).1)ᵀ) * (incM F b.1)ᵀ = w
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, incM_mul_inv, Matrix.transpose_one, Matrix.mul_one]
  have e2 : incM F b.1 = Matrix.fromCols (incM F b.1.toCols₁) (incM F b.1.toCols₂) := by
    ext u v
    rcases v with v | v <;> rfl
  conv_lhs => rw [← e1, e2, Matrix.transpose_fromCols, ← Matrix.fromCols_toCols (frQ b w), Matrix.fromCols_mul_fromRows]

end PositivityTheory.SiegelWeilFormula.Ald

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SmallSA
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def cmbE (bs : Module.Basis (Fin 2) F E) (c : Fin 2 → AF F) : AE F E := ∑ t, c t • ((1 : AF F) ⊗ₜ[F] bs t)

theorem cmbE_eq (bs : Module.Basis (Fin 2) F E) (c : Fin 2 → AF F) :
    cmbE bs c = ∑ t, c t • (Algebra.TensorProduct.basis (AF F) bs) t := by
  simp [cmbE, Algebra.TensorProduct.basis_apply]

theorem repr_cmbE_apply (bs : Module.Basis (Fin 2) F E) (c : Fin 2 → AF F) (t : Fin 2) :
    (Algebra.TensorProduct.basis (AF F) bs).repr (cmbE bs c) t = c t := by
  rw [cmbE_eq, Module.Basis.repr_sum_self]

theorem cmbE_repr (bs : Module.Basis (Fin 2) F E) (z : AE F E) :
    cmbE bs (fun t => (Algebra.TensorProduct.basis (AF F) bs).repr z t) = z := by
  rw [cmbE_eq]
  exact (Algebra.TensorProduct.basis (AF F) bs).sum_repr z

def cmbB {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (y : Fin m × Fin n × Fin 2 → AF F) : Mx F E m n :=
  fun a i => cmbE bs fun t => y (a, i, t)

theorem crdB_cmbB {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (y : Fin m × Fin n × Fin 2 → AF F) :
    crdB bs (cmbB bs y) = y := by
  funext k
  simp only [crdB, cmbB, repr_cmbE_apply]

theorem cmbB_crdB {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (X : Mx F E m n) : cmbB bs (crdB bs X) = X := by
  funext a i
  simp only [cmbB, crdB, cmbE_repr]

def Lk {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (M : Matrix (Fin m) (Fin m) (AE F E)) (y : Fin m × Fin n × Fin 2 → AF F) :
    Fin m × Fin n × Fin 2 → AF F := crdB bs (M * cmbB bs y)

theorem Lk_crdB {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (M : Matrix (Fin m) (Fin m) (AE F E)) (X : Mx F E m n) :
    Lk bs M (crdB bs X) = crdB bs (M * X) := by rw [Lk, cmbB_crdB]

theorem Lk_one {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (y : Fin m × Fin n × Fin 2 → AF F) : Lk bs 1 y = y := by
  rw [Lk, Matrix.one_mul, crdB_cmbB]

theorem Lk_mul {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (M M' : Matrix (Fin m) (Fin m) (AE F E))
    (y : Fin m × Fin n × Fin 2 → AF F) : Lk bs (M * M') y = Lk bs M (Lk bs M' y) := by
  rw [Lk, Lk, Lk, cmbB_crdB, Matrix.mul_assoc]

theorem Lk_zero {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (M : Matrix (Fin m) (Fin m) (AE F E)) :
    Lk (n := n) bs M 0 = 0 := by
  have : cmbB (m := m) (n := n) bs 0 = 0 := by
    funext a i; simp [cmbB, cmbE]
  funext k
  simp [Lk, this, crdB]

def Lc {m : ℕ} (bs : Module.Basis (Fin 2) F E) (M : Matrix (Fin m) (Fin m) (AE F E)) (v : Fin m × Fin 2 → AF F) :
    Fin m × Fin 2 → AF F :=
  fun p => (Algebra.TensorProduct.basis (AF F) bs).repr ((M *ᵥ fun a => cmbE bs fun t => v (a, t)) p.1) p.2

theorem Lc_zero {m : ℕ} (bs : Module.Basis (Fin 2) F E) (M : Matrix (Fin m) (Fin m) (AE F E)) : Lc bs M 0 = 0 := by
  funext p
  have hz : (fun _ : Fin m => (0 : AE F E)) = 0 := rfl
  simp [Lc, cmbE, hz, Matrix.mulVec_zero]

theorem triple_index_symm_embedded {m n N : ℕ} (h : n + 1 = N) (a : Fin m) (j : Fin n) (t : Fin 2) :
    (eK m h).symm (a, em0 h j, t) = Sum.inl (a, j, t) := by
  rw [Equiv.symm_apply_eq]; rfl

theorem triple_index_symm_last {m n N : ℕ} (h : n + 1 = N) (a : Fin m) (t : Fin 2) :
    (eK m h).symm (a, i0 h, t) = Sum.inr (a, t) := by
  rw [Equiv.symm_apply_eq]; rfl

theorem Lk_eK {m n N : ℕ} (h : n + 1 = N) (bs : Module.Basis (Fin 2) F E) (M : Matrix (Fin m) (Fin m) (AE F E))
    (x : K1 m n → AF F) :
    Lk bs M (x ∘ (eK m h).symm) ∘ eK m h = Sum.elim (Lk bs M (x ∘ Sum.inl)) (Lc bs M (x ∘ Sum.inr)) := by
  funext k
  rcases k with ⟨a, j, t⟩ | ⟨a, t⟩
  · have hk : eK m h (Sum.inl (a, j, t)) = (a, em0 h j, t) := rfl
    simp only [Function.comp_apply, hk, Sum.elim_inl, Lk, crdB, cmbB, Matrix.mul_apply, triple_index_symm_embedded]
  · have hk : eK m h (Sum.inr (a, t)) = (a, i0 h, t) := rfl
    simp only [Function.comp_apply, hk, Sum.elim_inr, Lk, Lc, crdB, cmbB, Matrix.mul_apply, Matrix.mulVec,
      dotProduct, triple_index_symm_last]

end PositivityTheory.SiegelWeilFormula.Ald

end
end

