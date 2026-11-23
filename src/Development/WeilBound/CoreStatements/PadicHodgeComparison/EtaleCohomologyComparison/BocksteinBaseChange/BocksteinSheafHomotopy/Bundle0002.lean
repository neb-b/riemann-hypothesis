module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtProps
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.BocksteinLemmas
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.SheafSumLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.BockOf
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry CochainComplex CochainComplex.HomComplex

namespace CrystallineSemistableComparison

open GlobalTheory.EtC

def IsRedSh {Q q : ℕ} (h : q ∣ Q) (i : ℤ) (π : tw Q i ⟶ (restr (ZMod.castHom h (ZMod q))).obj (tw q i)) : Prop :=
  ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) (ξ : Prim q Γ(U, ⊤)), ξ.1 = ζ.1 ^ (Q / q) →
    Sec.map π (twGen i ζ) = (show Sec ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) U from twGen i ξ)

theorem dvdA (p a b : ℕ) : p ^ a ∣ p ^ (a + b) := pow_dvd_pow p (Nat.le_add_right a b)

theorem dvdB (p a b : ℕ) : p ^ b ∣ p ^ (a + b) := pow_dvd_pow p (Nat.le_add_left b a)

def InTwSeq : Prop := ∀ (p a b : ℕ) [Fact p.Prime] (i : ℤ),
  ∃ (π : tw (p ^ (a + b)) i ⟶ (restr (ZMod.castHom (dvdB p a b) (ZMod (p ^ b)))).obj (tw (p ^ b) i))
    (π' : tw (p ^ (a + b)) i ⟶ (restr (ZMod.castHom (dvdA p a b) (ZMod (p ^ a)))).obj (tw (p ^ a) i))
    (l : kernel π ⟶ (restr (ZMod.castHom (dvdA p a b) (ZMod (p ^ a)))).obj (tw (p ^ a) i)),
    IsRedSh (dvdB p a b) i π ∧ IsRedSh (dvdA p a b) i π' ∧ Epi π ∧ p ^ a • kernel.ι π = 0 ∧
      kernel.ι π ≫ π' = p ^ b • l

def InRedSh : Prop := ∀ (Q q : ℕ) [NeZero Q] [NeZero q] (h : q ∣ Q) (i : ℤ)
  (π : tw Q i ⟶ (restr (ZMod.castHom h (ZMod q))).obj (tw q i)), IsRedSh h i π →
  ∀ (E : Spc) (n : ℤ) (z : Ht Q E n i),
    restrH (ZMod.castHom h (ZMod q)) E (tw q i) n (red Q q E n i z) = HK.post _ ((chains _).obj E) π n z

theorem bock_of (hS : InTwSeq) (hR : InRedSh) : BocksteinInputFromFormal := by
  intro hF p a b _ X _ n i z hz
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have : NeZero (p ^ (a + b)) := ⟨pow_ne_zero _ hp⟩
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp⟩
  have : NeZero (p ^ b) := ⟨pow_ne_zero _ hp⟩
  obtain ⟨π, π', l, hπ, hπ', hepi, htor, hcomp⟩ := hS p a b i
  have hex : (ShortComplex.mk (kernel.ι π) π (kernel.condition π)).ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel π) }
  obtain ⟨c, hc⟩ := hF.a7 (ZMod (p ^ (a + b))) _ hex
  have e1 := hR _ _ (dvdB p a b) i π hπ (sch.obj X) n z
  rw [hz, map_zero] at e1
  obtain ⟨w', hw'⟩ := ((hc ((chains (ZMod (p ^ (a + b)))).obj (sch.obj X)) n).1 z).1 e1.symm
  subst hw'
  refine ⟨?_, ?_⟩
  · change p ^ a • HK.post _ _ (kernel.ι π) n w' = 0
    rw [← PostcompositionHomotopy.post_nsmul, htor, PostcompositionHomotopy.post_zero]
  · have hA := hF.a8 _ _ (ZMod.castHom (dvdA p a b) (ZMod (p ^ a))) (sch.obj X) (tw (p ^ a) i) n
    obtain ⟨v, hv⟩ := hA.2 (HK.post _ _ l n w')
    refine ⟨v, hA.1 ?_⟩
    rw [hR _ _ (dvdA p a b) i π' hπ' (sch.obj X) n, map_nsmul, hv]
    change HK.post _ _ π' n (HK.post _ _ (kernel.ι π) n w') = _
    rw [← PostcompositionHomotopy.post_comp, hcomp, PostcompositionHomotopy.post_nsmul]

end CrystallineSemistableComparison
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.SecMapZero
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace CrystallineSemistableComparison

open GlobalTheory.EtC

namespace WeightedPowerFormIntegrability

variable {R : Type} [CommRing R]

theorem secMap_zero {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} : Sec.map φ (0 : Sec F U) = 0 := map_zero _

theorem secRes_zero {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 := map_zero _

theorem mk_eq_of_ev (hS : E.InSch) {X : Scheme.{0}} {I : GlobalTheory.EtC.Cx R} {n : ℤ} (α β : Cocycle ((chains R).obj (sch.obj X)) I n)
    (h : ev α.1 0 n (by simp) X (𝟙 X) = ev β.1 0 n (by simp) X (𝟙 X)) :
    CohomologyClass.mk α = CohomologyClass.mk β := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub]
  refine ((hS R X I (n - 1) n (n + 1) (by omega) rfl).2 (α - β)).2.2 ⟨0, ?_⟩
  refine (secMap_zero _).trans ?_
  change (0 : Sec (I.X n) X) = GlobalTheory.EtC.CupSpec.evHom I n 0 n (by simp) X (𝟙 X) (α.1 - β.1)
  rw [map_sub]
  exact (sub_eq_zero.2 h).symm

theorem ev_pull_sch {X Y : Scheme.{0}} {I : GlobalTheory.EtC.Cx R} {n : ℤ} (f : Y ⟶ X) (α : Cocycle ((chains R).obj (sch.obj X)) I n) :
    ev (zcomp (Cocycle.ofHom ((chains R).map (sch.map f))) α (zero_add n)).1 0 n (by simp) Y (𝟙 Y) =
      Sec.res f (ev α.1 0 n (by simp) X (𝟙 X)) := by
  rw [GlobalTheory.EtC.CupSpec.ev_res]
  refine (GlobalTheory.EtC.CupSpec.ev_pull (sch.map f) α.1 0 n _ Y (show Sx (sch.obj Y) 0 Y from 𝟙 Y)).trans ?_
  congr 1

end WeightedPowerFormIntegrability


open WeightedPowerFormIntegrability in
theorem sum : SumInputFromFormal := by
  intro hF R _ F X r Y j hj n
  have hS := hF.et.sch
  constructor
  · intro x x' h
    rw [← sub_eq_zero]
    obtain ⟨α, hα⟩ := CohomologyClass.mk_surjective (x - x')
    have hz : ∀ s, pull R (sch.map (j s)) F n (x - x') = 0 := fun s => by
      rw [map_sub, sub_eq_zero]; exact congrFun h s
    rw [← hα] at hz ⊢
    have key : ∀ s, ∃ y : Sec ((res R F).X (n - 1)) (Y s),
        Sec.map ((res R F).d (n - 1) n) y = Sec.res (j s) (ev α.1 0 n (by simp) X (𝟙 X)) := by
      intro s
      obtain ⟨y, hy⟩ := ((hS R (Y s) (res R F) (n - 1) n (n + 1) (by omega) rfl).2
        (zcomp (Cocycle.ofHom ((chains R).map (sch.map (j s)))) α (zero_add n))).2.1 (hz s)
      exact ⟨y, hy.trans (ev_pull_sch (j s) α)⟩
    choose y hy using key
    obtain ⟨y0, hy0⟩ := (sec_sum ((res R F).X (n - 1)) j hj).2 y
    have hy0' : ∀ s, Sec.res (j s) y0 = y s := fun s => congrFun hy0 s
    refine ((hS R X (res R F) (n - 1) n (n + 1) (by omega) rfl).2 α).2.2 ⟨y0, ?_⟩
    apply (sec_sum ((res R F).X n) j hj).1
    funext s
    show Sec.res (j s) (Sec.map ((res R F).d (n - 1) n) y0) = Sec.res (j s) (ev α.1 0 n (by simp) X (𝟙 X))
    rw [GlobalTheory.EtC.CupSpec.map_res, hy0' s, hy s]
  · intro x
    choose α hα using fun s => CohomologyClass.mk_surjective (x s)
    obtain ⟨a0, ha0⟩ := (sec_sum ((res R F).X n) j hj).2 fun s => ev (α s).1 0 n (by simp) (Y s) (𝟙 (Y s))
    have ha0' : ∀ s, Sec.res (j s) a0 = ev (α s).1 0 n (by simp) (Y s) (𝟙 (Y s)) := fun s => congrFun ha0 s
    have hcl : Sec.map ((res R F).d n (n + 1)) a0 = 0 := by
      apply (sec_sum ((res R F).X (n + 1)) j hj).1
      funext s
      show Sec.res (j s) (Sec.map ((res R F).d n (n + 1)) a0) = Sec.res (j s) 0
      rw [GlobalTheory.EtC.CupSpec.map_res, ha0' s]
      exact (((hS R (Y s) (res R F) (n - 1) n (n + 1) (by omega) rfl).2 (α s)).1).trans (secRes_zero _).symm
    obtain ⟨β, hβ0, -⟩ := (hS R X (res R F) (n - 1) n (n + 1) (by omega) rfl).1 a0 hcl
    refine ⟨CohomologyClass.mk β, funext fun s => ?_⟩
    rw [← hα s]
    show CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map (sch.map (j s)))) β (zero_add n)) = _
    apply mk_eq_of_ev hS
    rw [ev_pull_sch, hβ0 X (𝟙 X), ← ha0' s]
    congr 1
    simp [Sec.res]

end CrystallineSemistableComparison
end
end

