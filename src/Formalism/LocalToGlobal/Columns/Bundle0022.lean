module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.Bundle0006
public import Formalism.LocalToGlobal.Columns.RowFormsLemmas
public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
public import Formalism.LocalToGlobal.Columns.Bundle0002
public import Formalism.LocalToGlobal.Columns.DecorationStabilizerTrivialUnipotent
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Formalism.LocalToGlobal.Columns.CoefColLemmas
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalToGlobal.Columns.RowForms
public import Formalism.LocalToGlobal.GlobalTheory.GL4.PDetAll
public import Formalism.LocalToGlobal.Columns.Bundle0021
public import Formalism.LocalToGlobal.Columns.Bundle0012
public import Formalism.LocalToGlobal.HermitianForms.Bundle0005
public import Formalism.LocalToGlobal.Columns.Bundle0018

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.InvariantSubspaceNonzeroXOfRegular
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.DivisionValues

section Idem

variable {K : Type} [Field K] {A : Type} [Group A] {M : Type} [Group M] [Fintype M]


end Idem

section Gen

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG) {A : Type} [Group A] [Fintype A]
  (ι : A →* GLG (E := X.E) (n := n) (SG := SG)) (hι : ∀ a w, (Λ w).NormBy (ι a w))
  {M : Type} [Group M] [Fintype M] (j : M →* A) (ε : M →* X.Kˣ)

end Gen

section StabComb

variable (κ : Type) [CommRing κ] {n : ℕ}

variable {κ}

end StabComb

section Stab

variable {E : Type} [Field E] [NumberField E] [StarRing E]

end Stab

section StabPt

variable {X : Fields} {n : ℕ} [NeZero n] {SG : Finset (HeightOneSpectrum (𝓞 X.E))}


end StabPt

section Scal

variable {E : Type} [Field E] [NumberField E]



end Scal

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)



end Rows

section ScalAct

variable {E : Type} [Field E] [NumberField E] [StarRing E]

end ScalAct

section RhoScal

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem tensorWeights_scalar_action (lam : ι → DomWeight n) (t : ι → Kˣ) :
    Formalism.L2.DIV.rhoK lam (fun τ => (brpSc K (t τ) : GL (Fin n) K)) =
      (∏ τ, ((t τ : K) ^ (∑ i, (lam τ).w i))) • (1 : Module.End K (VV K lam)) := by
  classical
  have key : ∀ S : Finset ι, Formalism.L2.DIV.rhoK lam (fun τ => if τ ∈ S then (brpSc K (t τ) : GL (Fin n) K) else 1) =
      (∏ τ ∈ S, ((t τ : K) ^ (∑ i, (lam τ).w i))) • (1 : Module.End K (VV K lam)) := by
    intro S
    refine Finset.induction_on S ?_ (fun a S ha ih => ?_)
    · have h0 : (fun τ : ι => if τ ∈ (∅ : Finset ι) then (brpSc K (t τ) : GL (Fin n) K) else 1) = 1 := by
        funext τ
        simp
      rw [h0, map_one, Finset.prod_empty, one_smul]
    · have h0 : (fun τ => if τ ∈ insert a S then (brpSc K (t τ) : GL (Fin n) K) else 1) =
          Pi.mulSingle a (brpSc K (t a) : GL (Fin n) K) * (fun τ => if τ ∈ S then (brpSc K (t τ) : GL (Fin n) K) else 1) := by
        funext τ
        by_cases hτ : τ = a
        · subst hτ
          simp [ha]
        · have h1 : τ ∈ insert a S ↔ τ ∈ S := by simp [hτ]
          simp only [Pi.mul_apply, Pi.mulSingle_eq_of_ne hτ, one_mul]
          by_cases h2 : τ ∈ S
          · rw [if_pos (h1.mpr h2), if_pos h2]
          · rw [if_neg (fun h => h2 (h1.mp h)), if_neg h2]
      rw [h0, map_mul, ih, Formalism.L2.GlobalTheoryTheory.TraceIntegrality.rhoK_single_scalar, Finset.prod_insert ha, smul_mul_smul, one_mul]
      rfl
  have h := key Finset.univ
  simp only [Finset.mem_univ, if_true] at h
  exact h

end RhoScal

section RhoScal2

variable {E : Type} [Field E] [NumberField E] [StarRing E] {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} [NeZero n]


end RhoScal2

section RowsScal

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)



end RowsScal

section LamKEv

end LamKEv

section RowsMain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)




end RowsMain

section RowsMainV

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)




end RowsMainV

section Card

variable {E : Type} [Field E] [NumberField E] [StarRing E]

end Card

section RowsCard

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end RowsCard

section NotFaithful

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)



end NotFaithful

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.LocalLevelIsKOneAtT
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure HCrd {X : Fields} (Pr : Primes X) (n : ℕ) {cls : Type} (L : cls → Submodule (𝓞 X.E) (Fin n → X.E)) where
  n' : ℕ
  hn : n' = n
  J : Matrix (Fin n') (Fin n') X.E
  hJ : J = 1
  f : ℕ
  hf : f = X.f
  bad : Set (HeightOneSpectrum (𝓞 X.F))
  hbad : bad = plUnder X.F Pr.vGs
  lat : cls → Submodule (𝓞 X.E) (Fin n' → X.E)
  hlat : ∀ c, lat c = Formalism.L2.Forms.reL hn.symm (L c)

structure LevPack {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (gp : Fin 2 → ℕ) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) {cls : Type} (stab : cls → Type)
    [∀ c, Group (stab c)] (lat : cls → Submodule (𝓞 E) (Fin n → E)) where
  lev : Formalism.L2.Forms.StepLevel F E hc.sig J T f bad
  cls : RecCls hc J lev.Lb lev.U stab lat
  bad_iff : ∀ v : HeightOneSpectrum (𝓞 F), v ∈ bad ↔ ((gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal)
  Uloc_g : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → ∀ x : GL (Fin n) (E ⊗[F] v.adicCompletion F),
    (x ∈ levelVL hc.sig J v lev.Lb ∧ ∀ y ∈ Formalism.L2.Herm.locL v lev.Lb, ∃ z ∈ Formalism.L2.Herm.locL v lev.Lb,
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y = (gp i : E ⊗[F] v.adicCompletion F) • z) → x ∈ lev.Uloc v
  UlocAlt : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → ∀ x : GL (Fin n) (E ⊗[F] v.adicCompletion F), x ∈ lev.Uloc v ↔
    (x ∈ levelVL hc.sig J v lev.Lb ∧
      ∀ y ∈ Formalism.L2.Herm.locL v (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J lev.Lb)),
        (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈ Formalism.L2.Herm.locL v lev.Lb)

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)

def LocalLevelIsKOneAtT : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 X.F), (Pr.T u : 𝓞 X.F) ∈ v.asIdeal → ∀ x : GL (Fin n) (X.E ⊗[X.F] v.adicCompletion X.F),
    x ∈ levLoc hc n (Pr.vT u) Pr.vGs Λ.grp v ↔
    (x ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) X.E) v (baseLb X.E n (Pr.vT u)) ∧
      ∀ y ∈ Formalism.L2.Herm.locL v (Submodule.span (𝓞 X.E)
          (dualSet (hc.sig : X.E →+* X.E) (1 : Matrix (Fin n) (Fin n) X.E) (baseLb X.E n (Pr.vT u)))),
        (x : Matrix (Fin n) (Fin n) (X.E ⊗[X.F] v.adicCompletion X.F)) *ᵥ y - y ∈ Formalism.L2.Herm.locL v (baseLb X.E n (Pr.vT u)))


include hc hPr in
theorem th_plUnder_vGs (v : HeightOneSpectrum (𝓞 X.F)) :
    v ∈ plUnder X.F Pr.vGs ↔ ((Pr.g 0 : 𝓞 X.F) ∈ v.asIdeal ∨ (Pr.g 1 : 𝓞 X.F) ∈ v.asIdeal) := by
  classical
  have key : ∀ (i : Fin 2), v ∈ plUnder X.F (Pr.vG i) ↔ (Pr.g i : 𝓞 X.F) ∈ v.asIdeal := by
    intro i
    have h0 : X.conjO (Pr.piG i) ≠ 0 := by
      intro h
      have h1 := hPr.piG_norm i
      rw [h, mul_zero] at h1
      exact (Nat.cast_ne_zero.2 (hPr.g_prime i).ne_zero) h1.symm
    refine mem_plUnder_iff_norm hc (fun P => mem_divs h0 P) (Pr.g i) ?_ v
    have h2 : cO X.E (X.conjO (Pr.piG i)) = Pr.piG i := cO_cO _
    rw [h2, mul_comm]
    exact hPr.piG_norm i
  rw [← key 0, ← key 1]
  constructor
  · rintro ⟨P, hP, h⟩
    rcases Finset.mem_union.1 hP with h' | h'
    · exact Or.inl ⟨P, h', h⟩
    · exact Or.inr ⟨P, h', h⟩
  · rintro (⟨P, hP, h⟩ | ⟨P, hP, h⟩)
    · exact ⟨P, Finset.mem_union_left _ hP, h⟩
    · exact ⟨P, Finset.mem_union_right _ hP, h⟩

variable (c₀ : DiaG (E := X.E) (ST := Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet (E := X.E) (n := n) (ST := Pr.vT u) (SG := Pr.vGs))

def levPack₁ (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (hK : LocalLevelIsKOneAtT hc u Λ) :
    LevPack hc n (1 : Matrix (Fin n) (Fin n) X.E) Pr.g (Pr.T u) X.f (plUnder X.F Pr.vGs)
      (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) (fun c => (s c).1.L) where
  lev := tieLev hc hX hPr σ₀ u Λ
  cls := recCls hc n (Pr.vT u) Pr.vGs Λ.grp hS c₀ s hs
  bad_iff := th_plUnder_vGs hc hPr
  Uloc_g := fun i v hv x hx => by
    refine levLoc_of_princ hc n (Pr.vT u) Pr.vGs Λ.grp v (Pr.g i) ?_ ?_ x hx.1 hx.2
    · intro hT
      have h1 : (Pr.T u : 𝓞 X.F) ∈ v.asIdeal :=
        (mem_plUnder_iff_norm hc (rls_vT_iff hX hPr u) (Pr.T u) (hPr.piT_norm u) v).1 hT
      exact rls_T_notUnder hPr u v h1 ((th_plUnder_vGs hc hPr v).2 (by fin_cases i; exact Or.inl hv; exact Or.inr hv))
    · intro w _ hov
      have : (Pr.g i : 𝓞 X.F) ∈ w.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) := hov ▸ hv
      rwa [Ideal.mem_comap, map_natCast] at this
  UlocAlt := hK

def levPack (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (hK : LocalLevelIsKOneAtT hc u Λ) (H : HCrd Pr n fun c => (s c).1.L) :
    LevPack hc H.n' H.J Pr.g (Pr.T u) H.f H.bad (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) H.lat := by
  obtain ⟨n', hn, J, rfl, f, rfl, bad, rfl, lat, hlat⟩ := H
  subst hn
  obtain rfl : lat = fun c => (s c).1.L := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact levPack₁ hc hX hPr σ₀ u Λ c₀ s hS hs hK

end Gen

section Repack

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {hc : CMData F E}
  {S : HSpace E} {gp : Fin 2 → ℕ} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} {cls : Type} {stab : cls → Type}
  [∀ c, Group (stab c)] {lat : cls → Submodule (𝓞 E) S.V}

def LevPack.toStep (P : LevPack hc S.rank S.gram gp T f bad stab fun c => Formalism.L2.Herm.crdLat S (lat c)) :
    Formalism.L2.Herm.StepLevel hc S gp T f where
  Lb := P.lev.Lb
  Lb_fin := P.lev.Lb_fin
  Lb_span := P.lev.Lb_span
  Lb_int := fun x hx => Submodule.subset_span (P.lev.Lb_int x hx)
  Lb_dual := fun y hy => by
    refine Submodule.span_induction (p := fun y _ => (T : E) • y ∈ P.lev.Lb) (fun y hy => P.lev.Lb_dual y hy) ?_ ?_ ?_ hy
    · rw [smul_zero]; exact zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact add_mem ha hb
    · intro r a _ ha; rw [smul_comm]; exact Submodule.smul_mem _ _ ha
  Lb_index := P.lev.Lb_index
  Uloc := P.lev.Uloc
  Uloc_lev := P.lev.Uloc_lev
  Uloc_hyp := fun v h0 h1 hT => P.lev.Uloc_hyp v (fun hb => ((P.bad_iff v).1 hb).elim h0 h1) hT
  Uloc_g := P.Uloc_g
  UlocAlt := P.UlocAlt
  U := P.lev.U
  U_eq := P.lev.U_eq

def LevPack.toCls (P : LevPack hc S.rank S.gram gp T f bad stab fun c => Formalism.L2.Herm.crdLat S (lat c)) :
    Formalism.L2.Herm.ClassTie hc S P.toStep.Lb P.toStep.U stab lat where
  y := P.cls.y
  y_bij := P.cls.y_bij
  y_lat := P.cls.y_lat
  stabI := P.cls.stabI
  stabI_inj := P.cls.stabI_inj
  stabI_range := fun c γ => P.cls.stabI_range c γ.1 γ.2

end Repack

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.MultiFactorialEqTripleProd
section
open NumberField IsDedekindDomain Module MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN Formalism.L2.Forms

section Main

variable (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)

end Main

section Mono

theorem fock_norm_rational_eq {σ : Type} (P : MvPolynomial σ ℚ) : fockN (map (algebraMap ℚ ℂ) P) = ((Formalism.GradedWeylDivisibility.fockQ P P : ℚ) : ℝ) := by
  unfold fockN Formalism.GradedWeylDivisibility.fockQ
  rw [support_map_of_injective _ (algebraMap ℚ ℂ).injective]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_map, mfact]
  have : ‖(algebraMap ℚ ℂ) (AddMonoidAlgebra.coeff P m)‖ ^ 2 = ((AddMonoidAlgebra.coeff P m : ℚ) : ℝ) * ((AddMonoidAlgebra.coeff P m : ℚ) : ℝ) := by
    rw [eq_ratCast, Complex.norm_ratCast, sq_abs]
    ring
  rw [this]
  push_cast
  rfl

variable {ι : Type} [Fintype ι] {n : ℕ}

end Mono

section Gen

open Formalism.HermitianLattices.TraceIntegrality

variable (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] {ι : Type} [Fintype ι]

end Gen

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedVal
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RatSpanG {K : Type} [Field K] (s : K →+* ℂ) {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) :
    AddSubgroup (MvPolynomial (ι × Fin n × Fin n) ℂ) :=
  AddSubgroup.closure {p | ∃ (r : K) (f : ι → MvPolynomial (Fin n × Fin n) ℤ),
    (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧
    p = s r • Formalism.L2.Forms.ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ))}

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

theorem lamTrue_eq_shW (u : Pr.Word) (i : ℕ) :
    W.lamTrue u i = fun τ => shW (W.lamN u i τ) ((i * (R.t + 1) / 2 : ℕ) : ℤ) := by
  funext τ
  have h : ((i * (R.t + 1) / 2 : ℕ) : ℤ) = (i : ℤ) * (((R.t + 1) / 2 : ℕ) : ℤ) := by
    obtain ⟨b, hb⟩ := R.t_odd
    have h2 : R.t + 1 = 2 * (b + 1) := by omega
    rw [h2, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), Nat.mul_left_comm, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    push_cast
    ring
  unfold Wts.lamTrue shiftW shW
  congr 1
  funext x
  rw [h]
  ring

end Gen

section Rec

variable {d : ColDat} (a : ColArgs d)

theorem lamT_eq (u : d.what₂.Word) (i : ℕ) : CF.lamT (D := d.colRec a) u i = d.W.lamTrue u i :=
  (lamTrue_eq_shW (Pr := d.Pr) d.W u i).symm

end Rec

end Formalism.L2.Col
end
end

