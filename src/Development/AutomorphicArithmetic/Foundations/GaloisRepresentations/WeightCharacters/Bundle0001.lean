module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0201
public import Formalism.GradedWeylDivisibility.FinalC
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundTheorem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0225
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0443

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.AutCrit
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.autCrit_of :
    UpperTheory.Gal.Wt.AutCrit := by
  intro E _ _ _ a C hLev φ hL hC hI S hS hSub
  obtain ⟨N, hNo, hN1, hNC⟩ := hLev.isOpen
  set Wn : Set (UA E a) := GlobalTheory.EllU.finPart ⁻¹' N with hWn
  have hWo : IsOpen Wn := hNo.preimage GlobalTheory.EllU.continuous_finPart
  have hW1 : (1 : UA E a) ∈ Wn := by
    change GlobalTheory.EllU.finPart 1 ∈ N
    rw [map_one]; exact hN1
  have hkey : ∀ g, ∀ w ∈ Wn, φ (g * w) = φ (g * ((GlobalTheory.EllU.finPart w)⁻¹ * w)) := by
    intro g w hw
    have hkC : GlobalTheory.EllU.finPart w ∈ C := hNC ⟨hw, GlobalTheory.EllU.finPart_mem w⟩
    have hx := GlobalTheory.EllU.inv_finPart_mul_mem w
    have hcm := GlobalTheory.DefU.fin_mul_inf (GlobalTheory.EllU.finPart_mem w) hx
    have e : g * w = g * ((GlobalTheory.EllU.finPart w)⁻¹ * w) * GlobalTheory.EllU.finPart w := by
      rw [mul_assoc, ← hcm]; group
    rw [e, hC _ hkC]
  refine ⟨?_, hL, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun g => ?_
    have hc : Continuous fun y : UA E a => g⁻¹ * y := continuous_const.mul continuous_id
    have hX : Continuous fun y : UA E a => (⟨(GlobalTheory.EllU.finPart (g⁻¹ * y))⁻¹ * (g⁻¹ * y),
        GlobalTheory.EllU.inv_finPart_mul_mem _⟩ : infU E a) :=
      Continuous.subtype_mk (((GlobalTheory.EllU.continuous_finPart.comp hc).inv).mul hc) _
    have h0 : ContinuousAt (fun y : UA E a => φ (g * ((GlobalTheory.EllU.finPart (g⁻¹ * y))⁻¹ * (g⁻¹ * y)))) g :=
      ((hI g).comp hX).continuousAt
    refine h0.congr ?_
    have hm : Wn ∈ nhds (g⁻¹ * g) := by
      rw [inv_mul_cancel]; exact hWo.mem_nhds hW1
    filter_upwards [hc.continuousAt.preimage_mem_nhds hm] with y hy
    have := hkey g _ hy
    rw [mul_inv_cancel_left] at this
    exact this.symm
  · refine GlobalTheory.CuspRep.isOpen_stab_of_mem_nhds ((RU E a).comp (finU (E := E) (n := a)).subtype) _ ?_
    have ho : IsOpen ((Subtype.val : finU (E := E) (n := a) → UA E a) ⁻¹' Wn) := hWo.preimage continuous_subtype_val
    refine Filter.mem_of_superset (ho.mem_nhds hW1) fun k hk => ?_
    have hk' : (k : UA E a) ∈ C := by
      refine hNC ⟨?_, k.2⟩
      have : GlobalTheory.EllU.finPart (k : UA E a) ∈ N := hk
      rwa [GlobalTheory.EllU.finPart_of_finU k.2] at this
    funext g
    exact hC _ hk' g
  · haveI := hS
    refine Submodule.finiteDimensional_of_le (S₂ := S) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact hSub k k.2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.AutMul
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private theorem RU_mul' {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (x : UA E a) (φ ψ : UA E a → ℂ) :
    RU E a x (fun g => φ g * ψ g) = RU E a x φ * RU E a x ψ := by
  ext g
  rfl

theorem UpperTheory.Gal.Wt.autMul_of :
    UpperTheory.Gal.Wt.AutMul := by
  intro E _ _ _ a φ ψ hφ hψ
  refine ⟨hφ.cont.mul hψ.cont, fun γ hγ g => ?_, ?_, ?_⟩
  · change φ (γ * g) * ψ (γ * g) = φ g * ψ g
    rw [hφ.left γ hγ, hψ.left γ hγ]
  · refine isOpen_stab_of_mem_nhds ((RU E a).comp (finU (E := E) (n := a)).subtype) (fun g => φ g * ψ g) ?_
    refine Filter.mem_of_superset ((hφ.level.inter hψ.level).mem_nhds ⟨?_, ?_⟩) fun k hk => ?_
    · change RU E a 1 φ = φ
      simp
    · change RU E a 1 ψ = ψ
      simp
    · have h1 : RU E a k φ = φ := hk.1
      have h2 : RU E a k ψ = ψ := hk.2
      change RU E a k (fun g => φ g * ψ g) = fun g => φ g * ψ g
      rw [RU_mul', h1, h2]
      rfl
  · haveI := hφ.kfin
    haveI := hψ.kfin
    have f1 : (Submodule.span ℂ (Set.range fun k : infU E a => RU E a k φ)).FG :=
      Submodule.fg_iff_finiteDimensional _ |>.2 inferInstance
    have f2 : (Submodule.span ℂ (Set.range fun k : infU E a => RU E a k ψ)).FG :=
      Submodule.fg_iff_finiteDimensional _ |>.2 inferInstance
    haveI : FiniteDimensional ℂ ↥(Submodule.span ℂ (Set.range fun k : infU E a => RU E a k φ) *
        Submodule.span ℂ (Set.range fun k : infU E a => RU E a k ψ)) :=
      Submodule.fg_iff_finiteDimensional _ |>.1 (f1.mul f2)
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k : infU E a => RU E a k φ) *
        Submodule.span ℂ (Set.range fun k : infU E a => RU E a k ψ)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    change RU E a k (fun g => φ g * ψ g) ∈ _
    rw [RU_mul']
    exact Submodule.mul_mem_mul (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNearH
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt
open MvPolynomial

private theorem zp {k : Type} [NormedField k] [IsUltrametricDist k] {u : k} {ε : ℝ} (h0 : 0 ≤ ε) (hu : ‖u‖ = 1) (h : ‖u - 1‖ ≤ ε)
    (n : ℤ) : ‖u ^ n - 1‖ ≤ ε := by
  have hu0 : u ≠ 0 := fun e => by simp [e] at hu
  have step : ∀ w x : k, ‖w‖ = 1 → ‖w - 1‖ ≤ ε → ‖x - 1‖ ≤ ε → ‖x * w - 1‖ ≤ ε := fun w x hw h1 h2 => by
    rw [show x * w - 1 = (x - 1) * w + (w - 1) by ring]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ h1)
    rwa [norm_mul, hw, mul_one]
  induction n using Int.induction_on with
  | zero => simpa using h0
  | succ n ih => rw [zpow_add_one₀ hu0]; exact step _ _ hu h ih
  | pred n ih =>
    rw [zpow_sub_one₀ hu0]
    refine step _ _ (by rw [norm_inv, hu, inv_one]) ?_ ih
    rw [show u⁻¹ - 1 = -(u⁻¹ * (u - 1)) by field_simp; ring, norm_neg, norm_mul, norm_inv, hu, inv_one, one_mul]
    exact h

theorem UpperTheory.Gal.Wt.deltaNear_h : DeltaNear := by
  intro l _ ι a ν h hI
  let m : GL (Fin a) ℂ → Fin a × Fin a → Qbar l := fun g p => ι.symm ((g : Matrix (Fin a) (Fin a) ℂ) p.2 p.1)
  let D : MvPolynomial (Fin a × Fin a) ℤ := (Matrix.of fun i j => (X (j, i) : MvPolynomial (Fin a × Fin a) ℤ)).det
  have hmap : ∀ (w : Fin a × Fin a → ℂ) (P : MvPolynomial (Fin a × Fin a) ℤ),
      ι.symm (aeval w P) = aeval (fun j => ι.symm (w j)) P := by
    intro w P
    induction P using MvPolynomial.induction_on with
    | C n => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p j hp => simp [hp]
  have hD : ∀ g : GL (Fin a) ℂ, ι.symm (g : Matrix (Fin a) (Fin a) ℂ).det = aeval (m g) D := fun g => by
    rw [← hmap, AlgHom.map_det]
    congr 2
    ext i j
    simp
  have hδ : ∀ g : GL (Fin a) ℂ, ι.symm (delta ν g) = (aeval (m g) D) ^ ν.detShift * aeval (m g) (extremal ℤ a ν) := fun g => by
    have e1 : (aeval fun p : Fin a × Fin a => (1 : Matrix (Fin a) (Fin a) ℂ) p.1 p.2).comp
        (Formalism.GradedWeylDivisibility.rowAct ℂ (n := a) (g : Matrix (Fin a) (Fin a) ℂ).transpose) =
        aeval fun p : Fin a × Fin a => (g : Matrix (Fin a) (Fin a) ℂ) p.2 p.1 :=
      MvPolynomial.algHom_ext fun v => by simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.one_apply]
    have e2 : delta ν g = (g : Matrix (Fin a) (Fin a) ℂ).det ^ ν.detShift *
        aeval (fun p : Fin a × Fin a => (g : Matrix (Fin a) (Fin a) ℂ) p.2 p.1) (extremal ℤ a ν) := by
      change aeval _ (sqAct ℂ a ν g (extremal ℂ a ν)) = _
      rw [sqAct, map_smul, ← AlgHom.comp_apply, e1, detPow, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply,
        ← Formalism.L2.DIV.map_extremal (algebraMap ℤ ℂ), aeval_map_algebraMap, smul_eq_mul]
    rw [e2, map_mul, map_zpow₀, hD, hmap]
  have hm : ∀ p, ‖m h p‖ ≤ 1 := fun p => (hI _ _).1
  have hb : ∀ (x : Fin a × Fin a → Qbar l), (∀ p, ‖x p‖ ≤ 1) → ∀ P : MvPolynomial (Fin a × Fin a) ℤ, ‖aeval x P‖ ≤ 1 :=
    fun x hx P => (aeval_sub_le le_rfl hx hx (fun _ => by simp) P).1
  have hd1 : ‖aeval (m h) D‖ = 1 := by
    have h1 := hb _ hm D
    have h2 := hb (m h⁻¹) (fun p => (hI _ _).2) D
    have h3 : ‖aeval (m h) D‖ * ‖aeval (m h⁻¹) D‖ = 1 := by
      rw [← norm_mul, ← hD, ← hD, ← map_mul, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, map_one, norm_one]
    nlinarith [norm_nonneg (aeval (m h) D), norm_nonneg (aeval (m h⁻¹) D)]
  refine ⟨by rw [hδ, norm_mul, norm_zpow, hd1, one_zpow, one_mul]; exact hb _ hm _, fun ε hε hN => ?_⟩
  have h1 : ∀ p, ‖m 1 p‖ ≤ 1 := fun p => by
    simp only [m, Units.val_one, Matrix.one_apply]
    split_ifs <;> simp
  have hc : ∀ p, ‖m h p - m 1 p‖ ≤ ε := fun p => by
    have := hN p.2 p.1
    rwa [map_sub] at this
  have eD : aeval (m 1) D = 1 := by rw [← hD]; simp
  have eE : aeval (m 1) (extremal ℤ a ν) = 1 := by
    rw [extremal, Formalism.GradedWeylDivisibility.hw, map_prod]
    refine Finset.prod_eq_one fun s _ => ?_
    rw [map_pow, Formalism.GradedWeylDivisibility.lpMinor, AlgHom.map_det]
    rw [show ∀ M : Matrix (Fin (s.val + 1)) (Fin (s.val + 1)) (Qbar l), M = 1 → M.det ^ (ν.natW s - Formalism.GradedWeylDivisibility.nuNext ν.natW s) = 1 from
      fun M hM => by rw [hM, Matrix.det_one, one_pow]]
    ext i j
    simp [m, Matrix.one_apply, eq_comm]
  have c1 : ‖aeval (m h) D - 1‖ ≤ ε := by rw [← eD]; exact (aeval_sub_le hε hm h1 hc D).2.2
  have c2 : ‖aeval (m h) (extremal ℤ a ν) - 1‖ ≤ ε := by rw [← eE]; exact (aeval_sub_le hε hm h1 hc (extremal ℤ a ν)).2.2
  rw [map_sub, map_one, hδ, show ∀ x y : Qbar l, x * y - 1 = x * (y - 1) + (x - 1) from fun x y => by ring]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (zp hε hd1 c1 _))
  rwa [norm_mul, norm_zpow, hd1, one_zpow, one_mul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DomOf
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.dom_of :
    UpperTheory.Gal.Wt.Dom := by
  classical
  intro a κ f hf
  have hf' : f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ a a κ.natW := hf
  clear hf
  rw [Formalism.GradedWeylDivisibility.standardMonomialSpanDomain ℂ a a κ.natW] at hf'
  induction hf' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hx
    intro m hm k
    have h := (Formalism.GradedWeylDivisibility.bidetDominance ℂ a a K sz hsz I m hm).1 k
    rw [hshape] at h
    exact h
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm k
    rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
    · exact hx m h k
    · exact hy m h k
  | smul c x _ hx =>
    intro m hm k
    exact hx m (MvPolynomial.support_smul hm) k
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.EllCOf
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.ellC_of :
    UpperTheory.Gal.Wt.EllC := by
  intro E _ _ _ a C hC hneat
  set D : Subgroup (UA E a) := C ⊔ infU E a with hDdef
  have hDC : D ≤ C.comap GlobalTheory.EllU.finPart := sup_le (fun c hc => by
      change GlobalTheory.EllU.finPart c ∈ C
      rw [GlobalTheory.EllU.finPart_of_finU (hC hc)]; exact hc)
    (fun x hx => by
      change GlobalTheory.EllU.finPart x ∈ C
      rw [GlobalTheory.EllU.finPart_of_infU hx]; exact C.one_mem)
  let f : D →* C := (GlobalTheory.EllU.finPart.comp D.subtype).codRestrict C (fun d => hDC d.2)
  have hyp : ∀ g : UA E a, ∀ γ ∈ ratU E a, ∀ d : D, γ * g = g * d → f d = 1 := by
    intro g γ hγ d h
    have hfd : GlobalTheory.EllU.finPart (d : UA E a) ∈ C := hDC d.2
    have e : γ * g = g * GlobalTheory.EllU.finPart (d : UA E a) * ((GlobalTheory.EllU.finPart (d : UA E a))⁻¹ * (d : UA E a)) := by
      rw [h]; group
    have h1 := hneat g γ hγ _ hfd _ (GlobalTheory.EllU.inv_finPart_mul_mem (d : UA E a)) e
    exact Subtype.ext h1
  obtain ⟨ℓ, h1, h2⟩ := UpperTheory.Gal.Gen.ellGrp_holds (UA E a) C (ratU E a) D f hyp
  have hinf : ∀ x ∈ infU E a, ∀ g, ℓ (g * x) = ℓ g := by
    intro x hx g
    have e : f ⟨x, le_sup_right (a := C) hx⟩ = 1 := Subtype.ext (GlobalTheory.EllU.finPart_of_infU hx)
    have := h2 g ⟨x, le_sup_right (a := C) hx⟩
    simp only [e, mul_one] at this
    exact this
  have hC' : ∀ (c : C) g, ℓ (g * c) = ℓ g * c := by
    intro c g
    have e : f ⟨c, le_sup_left (b := infU E a) c.2⟩ = c := Subtype.ext (GlobalTheory.EllU.finPart_of_finU (hC c.2))
    have := h2 g ⟨c, le_sup_left (b := infU E a) c.2⟩
    simp only [e] at this
    exact this
  exact ⟨ℓ, ⟨h1, hC', hinf⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.EmbProjHolds
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

private theorem proj_of_sum {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : G → V →ₗ[ℂ] V)
    (A : Submodule ℂ V) (S : Set (Submodule ℂ V))
    (hSA : ∀ U ∈ S, U ≤ A) (hSs : ∀ U ∈ S, ∀ x, ∀ v ∈ U, ρ x v ∈ U)
    (hSi : ∀ U ∈ S, ∀ N ≤ U, (∀ x, ∀ v ∈ N, ρ x v ∈ N) → N = ⊥ ∨ N = U)
    (hAS : A ≤ sSup S) (ψ : V) (hψA : ψ ∈ A) (hψ : ψ ≠ 0) :
    ∃ U ∈ S, ∃ pr : V →ₗ[ℂ] V, pr ψ ≠ 0 ∧ ∀ f ∈ A, pr f ∈ U ∧ ∀ x, pr (ρ x f) = ρ x (pr f) := by
  classical
  let P : Set (Submodule ℂ V) := {C | C ≤ A ∧ (∀ x, ∀ v ∈ C, ρ x v ∈ C) ∧ ψ ∉ C}
  have hbot : (⊥ : Submodule ℂ V) ∈ P :=
    ⟨bot_le, fun x v hv => by rw [(Submodule.mem_bot ℂ).1 hv, map_zero]; exact zero_mem _,
      fun h => hψ ((Submodule.mem_bot ℂ).1 h)⟩
  obtain ⟨C, -, hC⟩ := zorn_le_nonempty₀ P (fun c hcP hc y hy => by
    have hdir : DirectedOn (· ≤ ·) c := hc.directedOn
    have hne : c.Nonempty := ⟨y, hy⟩
    refine ⟨sSup c, ⟨sSup_le fun z hz => (hcP hz).1, fun x v hv => ?_, fun h => ?_⟩, fun z hz => le_sSup hz⟩
    · obtain ⟨z, hz, hvz⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hv
      exact le_sSup hz ((hcP hz).2.1 x v hvz)
    · obtain ⟨z, hz, hvz⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 h
      exact (hcP hz).2.2 hvz) ⊥ hbot
  obtain ⟨hCA, hCs, hψC⟩ := hC.prop
  have hsup : ∀ N ≤ A, (∀ x, ∀ v ∈ N, ρ x v ∈ N) → ¬ N ≤ C → ψ ∈ C ⊔ N := by
    intro N hNA hNs hNC
    by_contra hn
    have hm : C ⊔ N ∈ P := ⟨sup_le hCA hNA, fun x v hv => by
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
      rw [map_add (f := _)]
      exact Submodule.add_mem_sup (hCs x a ha) (hNs x b hb), hn⟩
    exact hNC (le_sup_right.trans (hC.le_of_ge hm le_sup_left))
  obtain ⟨U, hUS, hUC⟩ : ∃ U ∈ S, ¬ U ≤ C := by
    by_contra hn
    push Not at hn
    exact hψC (sSup_le hn (hAS hψA))
  have hUs := hSs U hUS
  have hdisj : C ⊓ U = ⊥ := by
    rcases hSi U hUS (C ⊓ U) inf_le_right (fun x v hv => ⟨hCs x v hv.1, hUs x v hv.2⟩) with h | h
    · exact h
    · exact absurd (inf_eq_right.1 h) hUC
  have hψU := hsup U (hSA U hUS) hUs hUC
  have hAle : A ≤ C ⊔ U := by
    refine hAS.trans (sSup_le fun Y hY => ?_)
    by_cases hYC : Y ≤ C
    · exact hYC.trans le_sup_left
    have hYs := hSs Y hY
    rcases hSi Y hY ((C ⊔ U) ⊓ Y) inf_le_right (fun x v hv => ⟨by
        obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 hv.1
        rw [← e, map_add (f := _)]
        exact Submodule.add_mem_sup (hCs x a ha) (hUs x b hb), hYs x v hv.2⟩) with h | h
    · exfalso
      obtain ⟨c, hc, y, hy, e⟩ := Submodule.mem_sup.1 (hsup Y (hSA Y hY) hYs hYC)
      have hyCU : y ∈ C ⊔ U := by
        have : y = ψ - c := by rw [← e]; abel
        rw [this]
        exact sub_mem hψU (Submodule.mem_sup_left hc)
      have hy0 : y = 0 := (Submodule.mem_bot ℂ).1 (h ▸ (⟨hyCU, hy⟩ : y ∈ (C ⊔ U) ⊓ Y))
      rw [hy0, add_zero] at e
      exact hψC (e ▸ hc)
    · exact inf_eq_right.1 h
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl (C ⊔ U)
  have hc : IsCompl U (C ⊔ D) := by
    refine ⟨Submodule.disjoint_def.2 fun u hu hu' => ?_, ?_⟩
    · obtain ⟨c, hc, d, hd, e⟩ := Submodule.mem_sup.1 hu'
      have hdCU : d ∈ C ⊔ U := by
        have : d = u - c := by rw [← e]; abel
        rw [this]
        exact sub_mem (Submodule.mem_sup_right hu) (Submodule.mem_sup_left hc)
      have hd0 : d = 0 := Submodule.disjoint_def.1 hD.disjoint d hdCU hd
      rw [hd0, add_zero] at e
      have : u ∈ C ⊓ U := ⟨e ▸ hc, hu⟩
      rw [hdisj] at this
      exact (Submodule.mem_bot ℂ).1 this
    · rw [codisjoint_iff, ← top_le_iff, ← hD.sup_eq_top]
      exact sup_le (sup_le (le_sup_left.trans le_sup_right) le_sup_left) (le_sup_right.trans le_sup_right)
  let pr : V →ₗ[ℂ] V := U.subtype ∘ₗ Submodule.projectionOnto U (C ⊔ D) hc
  have hprU : ∀ u ∈ U, pr u = u := fun u hu =>
    congrArg Subtype.val (Submodule.projectionOnto_apply_left hc ⟨u, hu⟩)
  have hprC : ∀ c ∈ C, pr c = 0 := fun c hc' => by
    have h0 : Submodule.projectionOnto U (C ⊔ D) hc c = 0 :=
      Submodule.projectionOnto_apply_of_mem_right hc (Submodule.mem_sup_left hc')
    simp [pr, h0]
  have hform : ∀ c ∈ C, ∀ u ∈ U, pr (c + u) = u := fun c hc' u hu => by
    rw [map_add (f := _), hprC c hc', hprU u hu, zero_add]
  refine ⟨U, hUS, pr, ?_, fun f hf => ?_⟩
  · obtain ⟨c, hc', u, hu, e⟩ := Submodule.mem_sup.1 (hAle hψA)
    rw [← e, hform c hc' u hu]
    intro h0
    rw [h0, add_zero] at e
    exact hψC (e ▸ hc')
  · obtain ⟨c, hc', u, hu, rfl⟩ := Submodule.mem_sup.1 (hAle hf)
    refine ⟨by rw [hform c hc' u hu]; exact hu, fun x => ?_⟩
    rw [hform c hc' u hu, map_add (f := _), hform _ (hCs x c hc') _ (hUs x u hu)]

theorem embProj_holds : EmbProj := by
  intro E _ _ _ a τ U hU κ hκ u hu hu0
  obtain ⟨e, he⟩ := _root_.GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup E a τ
  obtain ⟨r, -, hr1, hr⟩ := _root_.GlobalTheory.DefU.exists_embRet E a τ
  let π : AutSub E a := ⟨U, hU⟩
  let s : Matrix.unitaryGroup (Fin a) ℂ →* UA E a := (embU a τ).subtype.comp e.symm.toMulEquiv.toMonoidHom
  have hs : ∀ y, cEmb τ (s y) = unitaryIncl a y := fun y => by
    have h3 := he (e.symm y)
    rw [e.apply_symm_apply] at h3
    exact h3.symm
  have hirr := isIrreducible_smallRep_unitary a κ
  obtain ⟨-, hsimple⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 hirr
  let S : Set (Submodule ℂ (UA E a → ℂ)) := {V | ∃ F : nablaSq ℂ a κ →ₗ[ℂ] (UA E a → ℂ), Function.Injective F ∧ (∀ w, F w ∈ U) ∧
    (∀ y w, F (sqRep ℂ a κ (unitaryIncl a y) w) = RU E a (s y) (F w)) ∧ V = LinearMap.range F}
  have hc : ∀ g, ∃ y, ∀ y', Commute ((s y)⁻¹ * g) (s y') := fun g =>
    ⟨e (r g), fun y => by
      change Commute ((((e.symm (e (r g))) : embU a τ) : UA E a)⁻¹ * g) ((e.symm y : embU a τ) : UA E a)
      rw [e.symm_apply_apply]
      exact hr g _⟩
  obtain ⟨f, hf⟩ : ∃ f : (smallRep (unitaryIncl a) κ).IntertwiningMap (π.rep.comp s), f ≠ 0 := by
    obtain ⟨-, F, hF0, hFm, hFi⟩ := hκ
    refine ⟨⟨F.codRestrict U hFm, fun y => ?_⟩, fun h0 => hF0 ?_⟩
    · ext v : 1
      apply Subtype.ext
      show F (sqRep ℂ a κ (unitaryIncl a y) v) = RU E a (s y) (F v)
      rw [← hs y]
      exact hFi (e.symm y) v
    · ext v : 1
      exact congrArg Subtype.val (DFunLike.congr_fun h0 v :)
  have htop := (_root_.GlobalTheory.CuspRep.CompUniq.isotypic _ _ _ _ _ π.rep s _ _ π.isIrreducible_rep hirr hirr hc f hf).1
  have hUS : U ≤ sSup S := by
    intro φ hφ
    have h1 : (⟨φ, hφ⟩ : U) ∈ (⨆ f : (smallRep (unitaryIncl a) κ).IntertwiningMap (π.rep.comp s), LinearMap.range f.toLinearMap) :=
      htop ▸ Submodule.mem_top
    refine (iSup_le (a := (sSup S).comap U.subtype) fun f' => ?_) h1
    rintro _ ⟨w, rfl⟩
    let F : nablaSq ℂ a κ →ₗ[ℂ] (UA E a → ℂ) := U.subtype ∘ₗ f'.toLinearMap
    have hF : ∀ y w, F (sqRep ℂ a κ (unitaryIncl a y) w) = RU E a (s y) (F w) := fun y w =>
      congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining _ _ f' y w)
    show F w ∈ sSup S
    rcases hsimple (LinearMap.ker F) (fun y x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      exact (hF y x).trans (by rw [hx, map_zero])) with h | h
    · exact le_sSup (show LinearMap.range F ∈ S from ⟨F, LinearMap.ker_eq_bot.1 h, fun w => (f' w).2, hF, rfl⟩) ⟨w, rfl⟩
    · have : w ∈ LinearMap.ker F := h ▸ Submodule.mem_top
      rw [LinearMap.mem_ker.1 this]
      exact zero_mem _
  obtain ⟨_, ⟨F, hinj, hFU, hF, rfl⟩, pr, h1, h2⟩ := proj_of_sum (fun y => RU E a (s y)) U S
    (by rintro _ ⟨F, -, hFU, -, rfl⟩ _ ⟨w, rfl⟩; exact hFU w)
    (by rintro _ ⟨F, -, -, hF, rfl⟩ y _ ⟨w, rfl⟩; exact ⟨_, hF y w⟩)
    (by
      rintro _ ⟨F, -, -, hF, rfl⟩ N hN hNs
      rcases hsimple (N.comap F) (fun y x hx => by
        show F _ ∈ N
        exact (hF y x).symm ▸ hNs y _ hx) with h | h
      · left
        rw [eq_bot_iff]
        intro φ hφ
        obtain ⟨w, rfl⟩ := hN hφ
        have : w ∈ N.comap F := hφ
        rw [h, Submodule.mem_bot] at this
        rw [this, map_zero]
        exact zero_mem _
      · right
        refine le_antisymm hN ?_
        rintro _ ⟨w, rfl⟩
        exact (h ▸ Submodule.mem_top : w ∈ N.comap F))
    hUS u hu hu0
  obtain ⟨G, hG⟩ := LinearMap.exists_leftInverse_of_injective F (LinearMap.ker_eq_bot.2 hinj)
  have hGF : ∀ w, G (F w) = w := fun w => LinearMap.congr_fun hG w
  refine ⟨G ∘ₗ pr, fun h0 => h1 ?_, fun x hx y hy => ?_⟩
  · obtain ⟨w, hw⟩ := (h2 u hu).1
    rw [LinearMap.comp_apply, ← hw, hGF] at h0
    rw [← hw, h0, map_zero]
  · obtain ⟨w, hw⟩ := (h2 y hy).1
    have hx' : s (e ⟨x, hx⟩) = x := congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)
    have h3 := (h2 y hy).2 (e ⟨x, hx⟩)
    rw [← hw, ← hF, ← hs, hx'] at h3
    rw [LinearMap.comp_apply, LinearMap.comp_apply, h3, ← hw, hGF, hGF]

end UpperTheory.Gal.Wt

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.QROf
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.qR_of :
    UpperTheory.Gal.Wt.QR := by
  intro a y
  obtain ⟨k, hk, b, hg, hb⟩ := GlobalTheory.T.iwasawa_unitary_upper_triangular (y : Matrix (Fin a) (Fin a) ℂ) y.isUnit
  let u : Matrix.unitaryGroup (Fin a) ℂ := ⟨k, hk⟩
  have hu : ((unitaryIncl a u : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) = k := rfl
  refine ⟨u, (unitaryIncl a u)⁻¹ * y, ?_, (mul_inv_cancel_left _ _).symm⟩
  have hbm : (((unitaryIncl a u)⁻¹ * y : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) = b := by
    rw [Units.val_mul, hg, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
  intro i j hij
  rw [hbm]
  exact hb hij
end

