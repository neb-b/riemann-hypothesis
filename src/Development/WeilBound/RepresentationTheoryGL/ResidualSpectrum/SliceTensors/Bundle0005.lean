module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0667
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0368
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0346
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0003
public import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ExistsHasInfCharGL
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin GlobalTheory.BCWords

namespace PositivityTheory.Rg.Rs.PInfInd2A

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem exists_scalar {N : ℕ} {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {z : Module.End ℂ (Sm E N)}
    (hz : z ∈ Zalg E N) (hc : ∀ o : Op E N, Commute z (act o)) : ∃ c : ℂ, ∀ φ ∈ V, z φ = c • φ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  set U := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E N) => z φ) '' Zalg E N) with hU
  have hfin : FiniteDimensional ℂ U := (hV.aut φ hφ).zfin
  have hle : U ≤ V := Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    exact Zalg_stable (fun X => hV.stable (.lie X)) hy φ hφ)
  have hst : ∀ x ∈ U, z x ∈ U := fun x hx => by
    have : U ≤ U.comap z := Submodule.span_le.2 (by
      rintro _ ⟨y, hy, rfl⟩
      exact Submodule.subset_span ⟨z * y, mul_mem hz hy, rfl⟩)
    exact this hx
  have hφU : φ ∈ U := Submodule.subset_span ⟨1, one_mem _, rfl⟩
  have : Nontrivial U := ⟨⟨φ, hφU⟩, 0, fun h => h0 (congrArg Subtype.val h)⟩
  obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue (z.restrict hst)
  obtain ⟨v, hv⟩ := hc'.exists_hasEigenvector
  have hv1 : z v.1 = c • v.1 := congrArg Subtype.val hv.apply_eq_smul
  refine ⟨c, fun ψ hψ => ?_⟩
  rcases hV.irred (V ⊓ z.eigenspace c) inf_le_left (fun o x hx => ⟨hV.stable o x hx.1, by
    have h1 : z x = c • x := Module.End.mem_eigenspace_iff.1 hx.2
    refine Module.End.mem_eigenspace_iff.2 ?_
    rw [← map_smul, ← h1]
    exact LinearMap.congr_fun (hc o).eq x⟩) with h | h
  · have : v.1 ∈ V ⊓ z.eigenspace c := ⟨hle v.2, Module.End.mem_eigenspace_iff.2 hv1⟩
    rw [h] at this
    exact absurd (Subtype.ext ((Submodule.mem_bot ℂ).1 this)) hv.2
  · rw [← h] at hψ
    exact Module.End.mem_eigenspace_iff.1 hψ.2

theorem exists_hasInfCharGL {N : ℕ} {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) (τ : E →+* ℂ) :
    ∃ m, HasInfCharGL V τ m := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ h0
  obtain ⟨m, hm, h⟩ := exists_multiset_qdet (Eop (a := N) τ) (((N : ℂ) - 1) / 2) φ f hf
  refine ⟨m, hm, fun u ψ hψ => ?_⟩
  obtain ⟨c, h1⟩ := exists_scalar hV (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩)
    (GlobalTheory.SpehInfChar.cap_commute_act τ u)
  have h2 : f (cap τ u φ) = _ := h u
  rw [h1 φ hφ, map_smul, hf, smul_eq_mul, mul_one] at h2
  rw [h1 ψ hψ, h2]

def blkV {n : Fin 2 → ℕ} (W₁ : Submodule ℂ (Sm E (n 0))) (W₂ : Submodule ℂ (Sm E (n 1))) :
    ∀ i : Fin 2, Submodule ℂ (Sm E (n i))
  | ⟨0, _⟩ => W₁
  | ⟨1, _⟩ => W₂

def blkE {n : Fin 2 → ℕ} {W₁ : Submodule ℂ (Sm E (n 0))} {W₂ : Submodule ℂ (Sm E (n 1))} (φ₁ : W₁) (φ₂ : W₂) :
    ∀ i : Fin 2, blkV W₁ W₂ i
  | ⟨0, _⟩ => φ₁
  | ⟨1, _⟩ => φ₂

theorem levPair_eta {R : Type} [CommRing R] {n : Fin 2 → ℕ} (m : ∀ i : Fin 2, GL (Fin (n i)) R) :
    CapFactor.levPair (m 0, m 1) = m := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

theorem tensorSp_of_tens2 {n : Fin 2 → ℕ} (W₁ : Submodule ℂ (Sm E (n 0))) (W₂ : Submodule ℂ (Sm E (n 1)))
    {T : GA E (n 0) × GA E (n 1) → ℂ} (hT : T ∈ tens2 W₁ W₂) :
    (fun m : ∀ i, GA E (n i) => T (m 0, m 1)) ∈ tensorSp (blkV W₁ W₂) := by
  let L : (GA E (n 0) × GA E (n 1) → ℂ) →ₗ[ℂ] ((∀ i, GA E (n i)) → ℂ) :=
    { toFun := fun F m => F (m 0, m 1), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hle : tens2 W₁ W₂ ≤ (tensorSp (blkV W₁ W₂)).comap L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨φ₁, h₁, φ₂, h₂, rfl⟩
    refine Submodule.subset_span ⟨blkE ⟨φ₁, h₁⟩ ⟨φ₂, h₂⟩, ?_⟩
    funext m
    change φ₁.1 (m 0) * φ₂.1 (m 1) = ∏ i : Fin 2, ((blkE (W₁ := W₁) (W₂ := W₂) ⟨φ₁, h₁⟩ ⟨φ₂, h₂⟩ i).1).1 (m i)
    rw [Fin.prod_univ_two]
    rfl
  exact hle hT

end PositivityTheory.Rg.Rs.PInfInd2A

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.FrobRecipHolds
section
noncomputable section

open GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.PRep

namespace PositivityTheory.Rg.Rs

namespace SliceFrobeniusReciprocity

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N c : ℕ} {n : Fin c → ℕ} {h : ∑ i, n i = N} {σ' : SmIrr (GL (Fin N) k)} {W : Type} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (∀ i, GL (Fin (n i)) k) W} {ℓ : σ'.V →ₗ[ℂ] W}

def frobFun (hℓ : ∀ (p : parab k (stdBlocks n h)) (v : σ'.V),
      ℓ (σ'.ρ p v) = ρ (leviProj k (stdBlocks n h) p) (ℓ v)) (v : σ'.V) :
    IndSp (stdBlocks n h) (twist ρ (deltaHalf k fun i => Fin (n i))⁻¹) :=
  ⟨⟨fun g => ℓ (σ'.ρ g v), fun p g => by
      show ℓ (σ'.ρ ((p : GL (Fin N) k) * g) v) = _
      rw [map_mul, Module.End.mul_apply, hℓ p]
      simp only [MonoidHom.coe_comp, Function.comp_apply, twist_apply, smul_smul, ← Units.val_mul,
        MonoidHom.inv_apply, mul_inv_cancel, Units.val_one, one_smul]⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset ((σ'.smooth v).mem_nhds (by simp)) fun g hg => by
      have hg' : σ'.ρ g v = v := hg
      show _ = _
      apply Subtype.ext
      funext x
      show ℓ (σ'.ρ (x * g) v) = ℓ (σ'.ρ x v)
      rw [map_mul, Module.End.mul_apply, hg'])⟩

theorem frobFun_apply (hℓ : ∀ (p : parab k (stdBlocks n h)) (v : σ'.V),
      ℓ (σ'.ρ p v) = ρ (leviProj k (stdBlocks n h) p) (ℓ v)) (v : σ'.V) (g : GL (Fin N) k) :
    (frobFun hℓ v).1.1 g = ℓ (σ'.ρ g v) := rfl

def frobMap (hℓ : ∀ (p : parab k (stdBlocks n h)) (v : σ'.V),
      ℓ (σ'.ρ p v) = ρ (leviProj k (stdBlocks n h) p) (ℓ v)) :
    σ'.ρ.IntertwiningMap (parInd (stdBlocks n h) (twist ρ (deltaHalf k fun i => Fin (n i))⁻¹)) where
  toLinearMap :=
    { toFun := frobFun hℓ
      map_add' := fun v v' => Subtype.ext (Subtype.ext (funext fun g => by
        show ℓ (σ'.ρ g (v + v')) = ℓ (σ'.ρ g v) + ℓ (σ'.ρ g v')
        simp))
      map_smul' := fun a v => Subtype.ext (Subtype.ext (funext fun g => by
        show ℓ (σ'.ρ g (a • v)) = a • ℓ (σ'.ρ g v)
        simp)) }
  isIntertwining' g := by
    ext v x
    show ℓ (σ'.ρ x (σ'.ρ g v)) = ℓ (σ'.ρ (x * g) v)
    rw [map_mul, Module.End.mul_apply]

end SliceFrobeniusReciprocity

open SliceFrobeniusReciprocity in
theorem frobRecip_holds : PositivityTheory.RSHS.LS.FrobRecip := by
  intro k _ _ _ _ N c n h σ' W _ _ ρ ℓ hℓ0 hℓ
  refine ⟨frobMap hℓ, fun h0 => hℓ0 (LinearMap.ext fun v => ?_)⟩
  have h1 := congrArg (fun f : _ →ₗ[ℂ] _ => (f v).1.1 1) h0
  simpa [frobMap, frobFun_apply] using h1

end PositivityTheory.Rg.Rs

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.LocSubOf
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.PRep GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs.LsTop

open PositivityTheory.RSHS.LS

theorem comp_ne {G U V W : Type} [Monoid G] [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {a : Representation ℂ G U} {b : Representation ℂ G V} {c : Representation ℂ G W}
    (g : a.IntertwiningMap b) (hg : g.toLinearMap ≠ 0) (Φ : b.Equiv c) : ∃ f : a.IntertwiningMap c, f ≠ 0 := by
  refine ⟨Φ.toIntertwiningMap.comp g, fun h0 => hg ?_⟩
  refine LinearMap.ext fun v => Φ.toLinearEquiv.injective ?_
  have h1 := congrArg (fun q : a.IntertwiningMap c => q v) h0
  simpa using h1

theorem step1 (hR : RestrictAtPoint) (hP : ExistsProj) (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (N c : ℕ) (n : Fin c → ℕ) (h : ∑ i, n i = N) (π : ∀ i, CuspSub E (n i)) (w : HeightOneSpectrum (𝓞 E))
    (τ : ∀ i, SmIrr (GL (Fin (n i)) (w.adicCompletion E))) (hτ : ∀ i, (π i).IsLocComp w (τ i))
    (V : Submodule ℂ (Sm E N)) (hE : Emb V (· ∈ indForms h π)) (σ' : SmIrr (GL (Fin N) (w.adicCompletion E)))
    (hσ' : IsLocCompGL V w σ') :
    ∃ ℓ : σ'.V →ₗ[ℂ] PiTensorProduct ℂ fun i => (τ i).V, ℓ ≠ 0 ∧
      ∀ (p : parab (w.adicCompletion E) (stdBlocks n h)) (v : σ'.V),
        ℓ (σ'.ρ p v) = piTensor (fun i => (τ i).ρ) (leviProj (w.adicCompletion E) (stdBlocks n h) p) (ℓ v) := by
  obtain ⟨e, he1, he2, he3⟩ := hE
  obtain ⟨f, hf0, hfV, hfeq⟩ := hσ'
  let F : PositivityTheory.RSHS.LeviInductionForms.LocMaps (indForms h π) w σ'.ρ :=
    ⟨e ∘ₗ f, fun v => he1 _ (hfV v), fun g v => by
      simp only [LinearMap.comp_apply]
      rw [hfeq g v]
      exact he3 (.fin _) _ (hfV v)⟩
  have hF0 : F.1 ≠ 0 := by
    intro h0
    apply hf0
    refine LinearMap.ext fun v => ?_
    exact he2 _ (hfV v) (LinearMap.congr_fun h0 v)
  obtain ⟨L, hLT, hL0, hLeq⟩ := hR E N c n h π w σ'.V σ'.ρ F hF0
  obtain ⟨v0, hv0⟩ : ∃ v, L v ≠ 0 := by
    by_contra hc
    exact hL0 (LinearMap.ext fun v => not_not.1 fun hv => hc ⟨v, hv⟩)
  obtain ⟨p, hp0, hpeq⟩ := hP E c n π w τ hτ (L v0) (hLT v0) hv0
  refine ⟨p ∘ₗ L, fun h0 => hp0 (LinearMap.congr_fun h0 v0), fun q v => ?_⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hLeq q v]
  exact hpeq _ _ (hLT v)

theorem hst_rev (a d : ℕ) (i : Fin d) :
    ((-spehExp d i + a * spehExp d i : ℝ) : ℂ) =
      ((modExp (fun _ : Fin d => Fin a) i : ℤ) : ℂ) / 2 + (((d : ℂ) - 1) / 2 - ((i.rev : ℕ) : ℂ)) := by
  rw [PositivityTheory.RSHS.LocalComponentTwist.modExp_const, Fin.val_rev]
  have hi := i.2
  have hc : ((d - ((i : ℕ) + 1) : ℕ) : ℂ) = (d : ℂ) - ((i : ℕ) : ℂ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hc]
  unfold spehExp
  push_cast
  ring

theorem gen (hF : FrobRecip) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N a d : ℕ) (h : ∑ _ : Fin d, a = N) (σ : SmIrr (GL (Fin a) k)) (σ' : SmIrr (GL (Fin N) k))
    (ψ : Fin d → GL (Fin a) k →* ℂˣ)
    (hψ : ∀ i, ψ i = detChar (Fin a) (absPow k ((-spehExp d i + a * spehExp d i : ℝ) : ℂ)))
    (ℓ : σ'.V →ₗ[ℂ] PiTensorProduct ℂ fun _ : Fin d => σ.V) (h0 : ℓ ≠ 0)
    (hℓ : ∀ (p : parab k (stdBlocks (fun _ : Fin d => a) h)) (v : σ'.V), ℓ (σ'.ρ p v) =
      piTensor (fun i => GlobalTheory.SmGL.twist σ.ρ (ψ i)) (leviProj k (stdBlocks (fun _ : Fin d => a) h) p) (ℓ v)) :
    ∃ hd : ∑ i : Fin d, (spehFactor (IrrGL.of σ.ρ σ.smooth σ.irred) d i.rev).1 = N,
      ∃ f : σ'.ρ.IntertwiningMap (prodIrr (fun i : Fin d => spehFactor (IrrGL.of σ.ρ σ.smooth σ.irred) d i.rev) hd),
        f ≠ 0 := by
  have hx := hF k N d (fun _ => a) h σ' (PiTensorProduct ℂ fun _ : Fin d => σ.V)
    (piTensor (Γ := fun _ : Fin d => GL (Fin a) k) (X := fun _ : Fin d => σ.V) fun i => GlobalTheory.SmGL.twist σ.ρ (ψ i)) ℓ h0 hℓ
  have hy := PositivityTheory.RSHS.LocalComponentTwist.levi_equiv σ.ρ (fun i : Fin d => ((d : ℂ) - 1) / 2 - ((i.rev : ℕ) : ℂ))
    (fun i => ((-spehExp d i + a * spehExp d i : ℝ) : ℂ)) (hst_rev a d) ψ hψ
  refine hx.elim fun g hg => hy.elim fun φ => ?_
  let T : ∀ i : Fin d, (GlobalTheory.SmGL.twist σ.ρ (detChar (Fin a) (absPow k (((d : ℂ) - 1) / 2 - ((i.rev : ℕ) : ℂ))))).Equiv
      (spehFactor (IrrGL.of σ.ρ σ.smooth σ.irred) d i.rev).rep := fun i =>
    (twistEquiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred) _).trans
      ((IrrGL.of σ.ρ σ.smooth σ.irred).twEquiv _ (isSmoothChar_absPow _))
  let M := multiProdEquiv (stdBlocks (fun _ : Fin d => a) h) T
  exact ⟨h, comp_ne g hg ((GlobalTheory.LocGL.parIndEquiv (stdBlocks (fun _ : Fin d => a) h) φ).symm.trans M)⟩

theorem locSub_of (hR : RestrictAtPoint) (hP : ExistsProj) (hF : FrobRecip) : LocSub :=
  fun E _ _ _ N a d V π _ _ hA w σ σ' hσ hσ' =>
    hA.elim fun h hA => hA.elim fun ν hA =>
      (step1 hR hP E N d (fun _ => a) h (fun i => π.twist (ν i)) w
        (fun i => σ.twist (CuspSub.locDet a (ν i) w) (CuspSub.isOpen_ker_locDet (ν i) w))
        (fun i => PositivityTheory.RSHS.LocalComponentTwist.isLocComp_twist π (ν i) hσ) V hA.2 σ' hσ').elim fun ℓ hℓ =>
      gen hF (w.adicCompletion E) N a d h σ σ' (fun i => CuspSub.locDet a (ν i) w)
        (fun i => congrArg (fun χ : (w.adicCompletion E)ˣ →* ℂˣ => χ.comp Matrix.GeneralLinearGroup.det)
          (PositivityTheory.RSHS.LocalComponentTwist.loc_eq_absPow (hA.1 i) w)) ℓ hℓ.1 hℓ.2

end PositivityTheory.Rg.Rs.LsTop

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PChord
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs

theorem chord_of : ExpTw → SqIntCrit → Chord := by
  intro hTw hSq E _ _ _ r s hr hs V c T lam hlam hT hp hb φ hφ k g
  have aut_tw {a : ℕ} {ψ : Sm E a} (h : IsAutForm ψ) (χ : HChar E) :
      IsAutForm (mulChi a χ ψ) := by
    exact {
      left γ g := by simp [h.left, chiDet_ratGL]
      level := isOpen_stab_of_mem_nhds _ _ <| Filter.mem_of_superset
        ((h.level.inter (isOpen_ker_chiDet χ)).mem_nhds ⟨by simp, by simp⟩) fun k hk => by
          have h1 : rt E a (finGL E a k) ψ = ψ := hk.1
          have h2 : chiDet a χ (finGL E a k) = 1 := hk.2
          change rt E a (finGL E a k) _ = _
          rw [rt_mulChi, h1, h2, Units.val_one, one_smul]
      kfin := by
        have := h.kfin
        refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k ψ)).map
          (GlobalTheory.CuspRep.mulChi a χ).toLinearMap) (Submodule.span_le.2 ?_)
        rintro _ ⟨k, rfl⟩
        exact ⟨_, Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩), (rt_mulChi χ _ ψ).symm⟩
      zfin := by
        have := h.zfin
        refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z ψ) ''
          Zalg E a)).map (GlobalTheory.CuspRep.mulChi a χ).toLinearMap) (Submodule.span_le.2 ?_)
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨z', h1, h2⟩ := Zalg_mulChi χ hz
        exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 ψ).symm⟩
      growth g := by
        obtain ⟨C, N, h1⟩ := h.growth g
        obtain ⟨C', N', h2⟩ := chiDet_growth (a := a) χ
        refine ⟨C * (‖((chiDet a χ g : ℂˣ) : ℂ)‖ * C'), N + N', fun y => ?_⟩
        rw [mulChi_apply, map_mul, Units.val_mul, norm_mul, norm_mul]
        refine (mul_le_mul (h1 y) (mul_le_mul_of_nonneg_left (h2 y) (norm_nonneg _)) (by positivity)
          ((norm_nonneg _).trans (h1 y))).trans_eq ?_
        ring }
  have hd : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hdR : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast hd
  unfold pE at hp
  push_cast at hp
  refine ⟨fun m₂ => ?_, fun m₁ => ?_⟩
  · obtain ⟨ψ₀, haut, hsl, hcen, hexp⟩ := hT.left φ hφ k g m₂
    refine ⟨mulChi r (Model.absC E (-(c / (r * (Module.finrank ℚ E : ℂ))))) ψ₀, aut_tw haut _, ?_,
      fun m₁ => by rw [ChordArithmetic.mulChi_absC_cancel, hsl]⟩
    refine hSq E r _ (aut_tw haut _) (ChordArithmetic.central_twist _ _ ?_ ψ₀ hcen) ?_
    · have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      have hd' : (Module.finrank ℚ E : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      field_simp
      ring
    · intro r₁ h1 h2 c₁ hc₁
      have h3 := hexp r₁ h1 h2 _ (hTw E r ψ₀ _ haut r₁ h1 h2 c₁ hc₁)
      have h4 := hb r₁ h1 (by omega) _ h3
      unfold pE at h4 ⊢
      rw [ChordArithmetic.left_eq _ _ _ _ _ hr.ne' hd.ne'] at h4
      push_cast at h4
      exact ChordArithmetic.left_arith r s r₁ _ lam _ _ (by exact_mod_cast hr) (by exact_mod_cast h1)
        (by exact_mod_cast h2) hlam hp h4
  · obtain ⟨ψ₀, haut, hsl, hcen, hexp⟩ := hT.right φ hφ k g m₁
    refine ⟨mulChi s (Model.absC E (-(-c / (s * (Module.finrank ℚ E : ℂ))))) ψ₀, aut_tw haut _, ?_,
      fun m₂ => by rw [ChordArithmetic.mulChi_absC_cancel, hsl]⟩
    refine hSq E s _ (aut_tw haut _) (ChordArithmetic.central_twist _ _ ?_ ψ₀ hcen) ?_
    · have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
      have hd' : (Module.finrank ℚ E : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      field_simp
      ring
    · intro r₂ h1 h2 c₂ hc₂
      have h3 := hexp r₂ h1 h2 _ (hTw E s ψ₀ _ haut r₂ h1 h2 c₂ hc₂)
      have h4 := hb (r + r₂) (by omega) (by omega) _ h3
      unfold pE at h4 ⊢
      rw [ChordArithmetic.right_eq _ _ _ _ _ hs.ne' hd.ne'] at h4
      push_cast at h4
      exact ChordArithmetic.right_arith r s r₂ _ lam _ _ (by exact_mod_cast hs) (by exact_mod_cast h1)
        (by exact_mod_cast h2) hlam hp h4

end PositivityTheory.Rg.Rs
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ProjOf
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs

open ParabolicProjection in
theorem proj_of (hP : Pr) (hT : SliceTens) (hI : IndMap) : Proj := by
  intro E _ _ _ r s _ _ V hV c z₁ z₂ T hTs hL2
  have hmem := hT E r s V hV c z₁ z₂ T hTs hL2
  obtain ⟨φ₀, hφ₀V, hφ₀⟩ := hTs.ne
  obtain ⟨k₀, g₀, m₀, hm₀⟩ := exists_slice_ne hφ₀ (hTs.unipInv φ₀ hφ₀V)
  obtain ⟨n, ψ₁, ψ₂, h₁, h₂, hsum⟩ := tensor_pair_finite_sum ((hmem φ₀ hφ₀V).2 k₀ g₀)
  have hne : ∑ i, (ψ₁ i).1 m₀.1 * (ψ₂ i).1 m₀.2 ≠ 0 := (hsum m₀) ▸ hm₀
  obtain ⟨hst₁, hsep₁⟩ := hP E r
  obtain ⟨hst₂, hsep₂⟩ := hP E s

  obtain ⟨χ₁, hχ₁, hχ₁e⟩ : ∑ i, (ψ₂ i).1 m₀.2 • ψ₁ i ∈ tw (A2 E r) z₁ :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h₁ i)
  have hχ₁0 : χ₁ ≠ 0 := fun h => sum_left_ne hne (by rw [← hχ₁e, h, map_zero])
  obtain ⟨V₁, p₁, hV₁, hp₁V, hp₁e, hp₁0⟩ := hsep₁ χ₁ hχ₁ hχ₁0
  have hf₁ : twMap r z₁ p₁ (∑ i, (ψ₂ i).1 m₀.2 • ψ₁ i) ≠ 0 := by
    rw [← hχ₁e]
    change twMap r z₁ p₁ (mulChi r (Model.absC E z₁) χ₁) ≠ 0
    rw [twMap_apply, mulChi_absC_neg, Ne, LinearEquiv.map_eq_zero_iff]
    exact hp₁0
  obtain ⟨b₁, hb₁⟩ := step_left (twMap r z₁ p₁) hf₁

  obtain ⟨χ₂, hχ₂, hχ₂e⟩ : ∑ i, (twMap r z₁ p₁ (ψ₁ i)).1 b₁ • ψ₂ i ∈ tw (A2 E s) z₂ :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h₂ i)
  have hχ₂0 : χ₂ ≠ 0 := fun h => sum_right_ne hb₁ (by rw [← hχ₂e, h, map_zero])
  obtain ⟨V₂, p₂, hV₂, hp₂V, hp₂e, hp₂0⟩ := hsep₂ χ₂ hχ₂ hχ₂0
  have hf₂ : twMap s z₂ p₂ (∑ i, (twMap r z₁ p₁ (ψ₁ i)).1 b₁ • ψ₂ i) ≠ 0 := by
    rw [← hχ₂e]
    change twMap s z₂ p₂ (mulChi s (Model.absC E z₂) χ₂) ≠ 0
    rw [twMap_apply, mulChi_absC_neg, Ne, LinearEquiv.map_eq_zero_iff]
    exact hp₂0
  obtain ⟨b₂, hb₂⟩ := step_right (twMap s z₂ p₂) hf₂

  obtain ⟨T', hT'e, hT'u, hT's⟩ := hI E r s V (tw (A2 E r) z₁) (tw (A2 E s) z₂) T (twMap r z₁ p₁) (twMap s z₂ p₂)
    hV.stable hV.aut (isStable_tw hst₁ z₁) (isStable_tw hst₂ z₂) hTs.equiv hmem (twMap_equiv hst₁ hp₁e)
    (twMap_equiv hst₂ hp₂e)
  refine ⟨V₁, V₂, hV₁, hV₂, T', fun φ hφ => ⟨hT'u φ hφ, fun k g => ?_⟩, inj_of_irred hV hT'e ⟨φ₀, hφ₀V, fun h => ?_⟩, hT'e⟩
  · obtain ⟨n', ψ₁', ψ₂', h₁', h₂', hs'⟩ := tensor_pair_finite_sum ((hmem φ hφ).2 k g)
    have e := hT's φ hφ k g n' ψ₁' ψ₂' h₁' h₂' hs'
    rw [show (fun m : GA E r × GA E s => (T' φ).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) *
      finGL E (r + s) g))) = fun m => ∑ i, (twMap r z₁ p₁ (ψ₁' i)).1 m.1 * (twMap s z₂ p₂ (ψ₂' i)).1 m.2 from funext e]
    exact sum_mem_tens2 (fun i => twMap_mem hp₁V _ (h₁' i)) (fun i => twMap_mem hp₂V _ (h₂' i))
  · have e := hT's φ₀ hφ₀V k₀ g₀ n ψ₁ ψ₂ h₁ h₂ hsum (b₁, b₂)
    rw [h] at e
    exact hb₂ e.symm

end PositivityTheory.Rg.Rs

end
end

