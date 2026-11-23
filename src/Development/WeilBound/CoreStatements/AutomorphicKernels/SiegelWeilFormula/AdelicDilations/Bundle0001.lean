module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FcCont
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.CntFalse
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem T_sub (d : SD σ) (Φ Φ' : d.Fn) : d.T (Φ - Φ') = d.T Φ - d.T Φ' := by
  funext X
  simp only [SD.T, Pi.sub_apply]
  rw [← map_sub]
  congr 1
  funext y
  simp [Darboux.rho, schr, mul_sub]

theorem vac_tens {d : SD σ} (R : RD d) (w : InfinitePlace F) (f : Mx F E d.m d.n → ℂ) (hf : f ∈ R.vac) :
    ∃ Ψ ∈ R.away w, f = R.tens w (fP 1) Ψ := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨g, hg, rfl⟩ := hf
    refine ⟨fun X => (∏ w' ∈ Finset.univ.erase w, fP 1 (R.loc w' X)) * g fun k => (d.crd X k).2,
      Submodule.subset_span ⟨fun _ => 1, g, hg, rfl⟩, ?_⟩
    funext X
    simp only [RD.tens]
    rw [← mul_assoc, Finset.mul_prod_erase _ (fun w' => fP 1 (R.loc w' X)) (Finset.mem_univ w)]
  | zero => exact ⟨0, zero_mem _, by funext X; simp [RD.tens]⟩
  | add f f' _ _ h h' =>
    obtain ⟨Ψ, hΨ, rfl⟩ := h
    obtain ⟨Ψ', hΨ', rfl⟩ := h'
    exact ⟨Ψ + Ψ', add_mem hΨ hΨ', by funext X; simp [RD.tens, mul_add]⟩
  | smul a f _ h =>
    obtain ⟨Ψ, hΨ, rfl⟩ := h
    exact ⟨a • Ψ, Submodule.smul_mem _ a hΨ, by funext X; simp [RD.tens]; ring⟩

theorem ndA (H : Hyps) {d : SD σ} (R : RD d) (hmn : d.m < d.n) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac)
    {U p Ê t} (hE : EData d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t) (j : ℕ) (hj : j ≤ p.rootMultiplicity (s0 d.m d.n)) :
    ∀ L ∈ d.lamSet, L (fun g => iteratedDeriv j (Ê · g) (s0 d.m d.n)) = 0 := by
  intro L hL
  have hK := H.polyKFin F E σ d R Φ hΦ ((H.vacK F E σ d R).2.1 hv)
  have hsec := H.secK F E σ d Φ hK
  have hEis := H.eisWk F E σ d _ _ hsec
  obtain ⟨hadd, hbd⟩ := H.lamBd F E σ d L hL
  obtain ⟨nb, lam, 𝓖, T, x, hc, hT, rfl⟩ := hL
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE
  obtain ⟨hDiff, hComm⟩ := lamDeriv (rat2 σ d.Y) _ hadd hbd U Ê hUo hd hcont hinv
  show fc d.B.ψ d.b nb lam 𝓖 (fun g => iteratedDeriv j (Ê · g) (s0 d.m d.n)) T x = 0
  rw [← hComm _ hs j]
  obtain ⟨t', ht'⟩ := H.unfold F E σ d _ _ hsec hEis
  obtain ⟨ε, w, hw, -⟩ := (H.auxEx F E σ d).2.1
  have hWL := H.whitLow F E σ d R hmn Φ hΦ hv nb lam 𝓖 hc ε w hw T hT x
  rw [zero_mul] at hWL
  have := ordVal U p (fun z => fc d.B.ψ d.b nb lam 𝓖 (Ê z) T x)
    (fun z => ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam) (max t t')
    (s0 d.m d.n) 0 hUo hR hs hp hDiff ?_ hWL j hj
  · rw [this, mul_zero]
  · intro z hz
    have h1 := (hfar z (lt_of_le_of_lt (le_max_left _ _) hz)).2
    have h2 := (ht' z (lt_of_le_of_lt (le_max_right _ _) hz) nb lam 𝓖 hc ε w hw x).2 T hT
    rw [← h2]
    simp only [fc, h1, mul_assoc]
    exact integral_const_mul _ _

theorem cnt_true (m : ℕ) : cnt (fun _ : Fin m => true) true = m := by
  simp [cnt]

theorem cnt_false (m : ℕ) : cnt (fun _ : Fin m => true) false = 0 := by
  simp [cnt]

theorem exists_isHolW_iteratedDeriv (H : Hyps) {d : SD σ} (R : RD d) (hmn : d.m < d.n) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac)
    {U : Set ℂ} {p : Polynomial ℂ} {Ê : ℂ → d.G → ℂ} {t : ℝ}
    (hE : EData d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t) (w : InfinitePlace F) (j : ℕ)
    (hj : j ≤ p.rootMultiplicity (s0 d.m d.n)) (hlow : ∀ i < j, ∀ g, iteratedDeriv i (Ê · g) (s0 d.m d.n) = 0) :
    ∃ (pp qq : ℕ) (e : ℤ), (pp = d.m ∧ qq = 0 ∨ pp = 0 ∧ qq = d.m) ∧
      ∀ g, IsHolW pp qq e fun y => iteratedDeriv j (Ê · (g * R.ι w y)) (s0 d.m d.n) := by
  obtain ⟨-, -, hTG, hLC, hT2, hSC⟩ := H.auxEx F E σ d
  have hE' := hE
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE'
  have hAc := famCont U Ê hUo hd hcont _ hs j
  have hAi : ∀ γ ∈ rat2 σ d.Y, ∀ g, iteratedDeriv j (Ê · (γ * g)) (s0 d.m d.n) = iteratedDeriv j (Ê · g) (s0 d.m d.n) :=
    fun γ hγ g => derivInv U Ê hUo _ hs γ g (fun z hz => hinv z hz γ hγ g) j
  obtain ⟨Ψ, hΨ, hTΨ⟩ := vac_tens R w _ hv
  obtain ⟨Lop, hLop⟩ := H.locOpEx F E σ d R w
  obtain ⟨φ, hφ⟩ := H.liftEx F E σ d R w Ψ hΨ
  obtain ⟨sL, ρ, pp, qq, e, -, hLD, hsL, -⟩ := H.locInst F E σ d R w Lop hLop
  have hΦφ : φ 1 = Φ := by
    have h0 := (H.tAll.1 F E σ d).2.2 (φ 1 - Φ) (sub_mem (hφ 1).1 hΦ) (by rw [T_sub, (hφ 1).2, hTΨ, sub_self])
    exact sub_eq_zero.1 h0
  have hpq : pp = d.m ∧ qq = 0 ∨ pp = 0 ∧ qq = d.m := by
    rcases hLD.sign with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
    · left; rw [h1, h2, cnt_true, cnt_false]; exact ⟨rfl, rfl⟩
    · right; rw [h1, h2, cnt_true, cnt_false]; exact ⟨rfl, rfl⟩
  refine ⟨pp, qq, e, hpq, ?_⟩
  haveI := hTG; haveI := hLC; haveI := hT2; haveI := hSC
  refine H.holLead d.m d.n pp qq e d.ok.hm hmn hpq d.G (par2 σ d.Y) (rat2 σ d.Y) (R.ι w) (s0 d.m d.n) d.Ht (d.sec0 Φ)
    (R.cont w) ?_ U p Ê t hUo hR hs hd hcont (fun z hz => ⟨(hfar z hz).1, fun g => (hfar z hz).2 g⟩) j hlow ?_
  · intro g
    obtain ⟨x, y, c, r, hr, hg, hxy⟩ := H.gSplit F E σ d R w Lop hLop Ψ hΨ φ hφ g
    refine ⟨x, y, c, r, hr, hg, fun y' => ⟨(hxy y').1, ?_⟩⟩
    rw [← hΦφ, (hxy y').2 1, ← hsL, hLD.vac]
  · intro ψ hψ nb hnb g a b
    exact H.lamSing F E σ d R w _ hAc hAi (ndA H R hmn hΦ hv hE j hj) ψ hψ nb hnb g a b

end PositivityTheory.SiegelWeilFormula.AStep

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FinOneAdr
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def adr [IsTotallyReal F] (w : InfinitePlace F) (r : ℝ) : AF F :=
  ((fun u => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal u)).symm (if u = w then r else 1),
    (1 : FiniteAdeleRing (𝓞 F) F)) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)

theorem adr_fst [IsTotallyReal F] (w u : InfinitePlace F) (r : ℝ) :
    (adr w r).1 u = (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal u)).symm (if u = w then r else 1) := rfl

theorem adr_snd [IsTotallyReal F] (w : InfinitePlace F) (r : ℝ) : (adr (F := F) w r).2 = 1 := rfl

theorem adr_mul [IsTotallyReal F] (w : InfinitePlace F) (r s : ℝ) : adr w r * adr w s = adr (F := F) w (r * s) := by
  refine Prod.ext (funext fun u => ?_) (mul_one _)
  show (adr w r).1 u * (adr w s).1 u = (adr w (r * s)).1 u
  rw [adr_fst, adr_fst, adr_fst, ← map_mul]
  congr 1
  split_ifs <;> simp

theorem adr_one [IsTotallyReal F] (w : InfinitePlace F) : adr (F := F) w 1 = 1 := by
  refine Prod.ext (funext fun u => ?_) rfl
  show (adr w 1).1 u = 1
  rw [adr_fst, ite_self, map_one]

theorem ext_adr [IsTotallyReal F] (w u : InfinitePlace F) (r : ℝ) :
    InfinitePlace.Completion.extensionEmbedding u ((adr w r).1 u) = ((if u = w then r else 1 : ℝ) : ℂ) := by
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal u), adr_fst]
  congr 1
  exact (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal u)).apply_symm_apply _

theorem finOne_adr [IsTotallyReal F] (w : InfinitePlace F) (r : ℝ) : finOne F * adr w r = finOne F := by
  refine Prod.ext ?_ (mul_one _)
  show (finOne F).1 * (adr w r).1 = (finOne F).1
  have h0 : (finOne F).1 = 0 := rfl
  rw [h0, zero_mul]

end PositivityTheory.SiegelWeilFormula.AStep

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.RatVCocompact
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace COneB

variable {d : SD σ} (L : LD d)

def Nu (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) := ∑ j, Matrix.single L.i₀ (L.em j) (u j)

theorem em_ne (j : Fin L.n) : L.em j ≠ L.i₀ := (L.rng (L.em j)).2 ⟨j, rfl⟩

theorem Nu_mul (u v : Fin L.n → AE F E) : Nu L u * Nu L v = 0 := by
  simp only [Nu, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
  apply Matrix.single_mul_single_of_ne
  exact em_ne L _

theorem Nu_add (u v : Fin L.n → AE F E) : Nu L (u + v) = Nu L u + Nu L v := by
  simp only [Nu, Pi.add_apply, Matrix.single_add, Finset.sum_add_distrib]

theorem Nu_cont : Continuous (Nu L) := by
  have e : Nu L = fun u => ∑ j, u j • Matrix.single L.i₀ (L.em j) (1 : AE F E) := by
    funext u; simp only [Nu, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e]
  exact continuous_finsetSum _ fun j _ => (continuous_apply j).smul continuous_const


omit L in
theorem unit_frame (d : SD σ) (x : d.G) : ∃ e : AE F E,
    (inFrame d.b x)ᵀ * Matrix.fromBlocks 0 1 (e • 1) 0 * (inFrame d.b x).map (cA σ) = Matrix.fromBlocks 0 1 (e • 1) 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  refine ⟨((ε : ℤ) : AE F E), ?_⟩
  have hF := kfour.frameEq_adelic (F := F) (Y := d.Y) hε
  have hU : (mat2 x)ᵀ * dbl (incM F d.Y.J) * (mat2 x).map (cA σ) = dbl (incM F d.Y.J) := x.2
  rw [SiegelEisensteinSeries.Grp.matrix_eq_frame_conjugate d.b x] at hU
  have h1 : (incM F d.b.1)ᵀ * (incM F (d.b⁻¹).1)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, SiegelEisensteinSeries.Grp.incM_inv_mul, Matrix.transpose_one]
  have h2 : (incM F (d.b⁻¹).1).map (cA σ) * (incM F d.b.1).map (cA σ) = 1 := by
    rw [← SiegelEisensteinSeries.Grp.map_cA_mul, SiegelEisensteinSeries.Grp.incM_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [← hF]
  conv_rhs => rw [← hU]
  rw [SiegelEisensteinSeries.Grp.map_cA_mul, SiegelEisensteinSeries.Grp.map_cA_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [h2, Matrix.mul_one, ← Matrix.mul_assoc (incM F d.b.1)ᵀ (incM F (d.b⁻¹).1)ᵀ, h1, Matrix.one_mul]

omit L in
theorem blk_unit (d : SD σ) (x : d.G) (a a' : Matrix (Fin d.n) (Fin d.n) (AE F E))
    (hx : inFrame d.b x = Matrix.fromBlocks a 0 0 a') : aᵀ * a'.map (cA σ) = 1 := by
  obtain ⟨e, he⟩ := unit_frame d x
  rw [hx] at he
  simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_zero,
    Matrix.map_zero _ (map_zero _), Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_one] at he
  have := (Matrix.fromBlocks_inj.1 he).2.1
  exact this

omit L in
theorem cA_cA_mat (d : SD σ) {p q : Type} (M : Matrix p q (AE F E)) : (M.map (cA σ)).map (cA σ) = M := by
  have hσ : ∀ a, σ (σ a) = a := kfour.sigma_sigma_of_good d.ok.good
  ext i j; simp [kfour.cA_cA' σ hσ]

theorem uM_frame {uM ν 𝓤} (hu : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) :
    inFrame d.b (uM u) = Matrix.fromBlocks (1 + Nu L u) 0 0 (((1 - Nu L u)ᵀ).map (cA σ)) := by
  obtain ⟨a', ha'⟩ := hu.1 u
  have ha : inFrame d.b (uM u) = Matrix.fromBlocks (1 + Nu L u) 0 0 a' := ha'
  rw [ha]
  have h1 := blk_unit d _ _ _ ha
  have h2 : (1 - Nu L u)ᵀ * (1 + Nu L u)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Nu_mul, sub_zero,
      sub_add_cancel, Matrix.transpose_one]
  have h3 : a'.map (cA σ) = (1 - Nu L u)ᵀ := by
    calc a'.map (cA σ) = ((1 - Nu L u)ᵀ * (1 + Nu L u)ᵀ) * a'.map (cA σ) := by rw [h2, Matrix.one_mul]
      _ = (1 - Nu L u)ᵀ * ((1 + Nu L u)ᵀ * a'.map (cA σ)) := by rw [Matrix.mul_assoc]
      _ = (1 - Nu L u)ᵀ := by rw [h1, Matrix.mul_one]
  have h4 : a' = ((1 - Nu L u)ᵀ).map (cA σ) := by rw [← h3, cA_cA_mat d]
  rw [h4]

theorem uM_add {uM ν 𝓤} (hu : L.UData uM ν 𝓤) (u v : Fin L.n → AE F E) : uM (u + v) = uM u * uM v := by
  apply kfour.inFrame_injective d.b
  rw [SiegelEisensteinSeries.Grp.inFrame_mul, uM_frame L hu, uM_frame L hu, uM_frame L hu, Matrix.fromBlocks_multiply]
  have e1 : (1 + Nu L u) * (1 + Nu L v) = 1 + Nu L (u + v) := by
    rw [Nu_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Nu_mul, add_zero]
    abel
  have e2 : ((1 - Nu L u)ᵀ).map (cA σ) * ((1 - Nu L v)ᵀ).map (cA σ) = ((1 - Nu L (u + v))ᵀ).map (cA σ) := by
    have hm := Matrix.map_mul (L := (1 - Nu L u)ᵀ) (M := (1 - Nu L v)ᵀ) (f := (cA σ).toRingHom)
    erw [← hm]
    rw [← Matrix.transpose_mul, Nu_add, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Nu_mul,
      sub_zero]
    congr 2
    abel
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, e1, e2]

theorem uM_zero {uM ν 𝓤} (hu : L.UData uM ν 𝓤) : uM 0 = 1 := by
  have h := uM_add L hu 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem uM_neg {uM ν 𝓤} (hu : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : (uM u)⁻¹ = uM (-u) := by
  have h := uM_add L hu (-u) u
  rw [neg_add_cancel, uM_zero L hu] at h
  exact (eq_inv_of_mul_eq_one_left h.symm).symm

theorem uM_cont {uM ν 𝓤} (hu : L.UData uM ν 𝓤) : Continuous uM := by
  have hcA : Continuous (cA σ : AE F E → AE F E) :=
    IsModuleTopology.continuous_of_linearMap (R := AF F) (cA σ).toLinearMap
  have hmat : Continuous fun u => mat2 (uM u) := by
    have e : (fun u => mat2 (uM u)) = fun u => incM F d.b.1 * Matrix.fromBlocks (1 + Nu L u) 0 0
        (((1 - Nu L u)ᵀ).map (cA σ)) * incM F (d.b⁻¹).1 := by
      funext u; rw [SiegelEisensteinSeries.Grp.matrix_eq_frame_conjugate d.b, uM_frame L hu]
    rw [e]
    refine (continuous_const.matrix_mul (Continuous.matrix_fromBlocks (continuous_const.add (Nu_cont L))
      continuous_const continuous_const ?_)).matrix_mul continuous_const
    exact ((continuous_const.sub (Nu_cont L)).matrix_transpose).matrix_map hcA
  have hinv : Continuous fun u => mat2 (uM u)⁻¹ := by
    simp only [uM_neg L hu]
    exact hmat.comp continuous_neg
  refine Topology.IsInducing.subtypeVal.continuous_iff.2 ?_
  exact Units.continuous_iff.2 ⟨hmat, hinv⟩

theorem ratV_cocompact : ∃ K : Set (Fin L.n → AE F E), IsCompact K ∧ ∀ u, ∃ r ∈ L.ratV, r + u ∈ K := by
  obtain ⟨C, hC, hCx⟩ := kfour.exists_compact_AE (F := F) (E := E)
  refine ⟨Set.univ.pi (fun _ => C), isCompact_univ_pi (fun _ => hC), fun u => ?_⟩
  choose x hx using fun j => hCx (u j)
  refine ⟨GlobalTheory.ThK.incV F x, AddSubgroup.subset_closure ⟨x, rfl⟩, fun j _ => ?_⟩
  simpa [GlobalTheory.ThK.incV] using hx j

end COneB

end PositivityTheory.SiegelWeilFormula.AStep

end
end

