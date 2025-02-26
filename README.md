## Welcome

This is the webpage for the course [*Preuve assistée par ordinateur dans Lean*](http://edinfomaths.universite-lyon.fr/these/cours-doctoraux) for the graduate school 
*ED InfoMath*, held in Lyon in February−March 2025.

### Teacher and schedule

The teacher is [me/Filippo A. E. Nuccio](https://perso.univ-st-etienne.fr/nf51454h/): I 
am Maître de Conférences at the [Université Jean Monnet Saint-Étienne](https://www.univ-st-etienne.fr/fr/index.html) and a member of the [Institut Camille Jordan](https://math.univ-lyon1.fr/icj/). 

Classes will typically be in English, but any question in French (or in Italian...) is 
welcome; chances are high that the answer, if within my competences, will be in the 
same language. Feel free to reach out to me for any 
question, either by <a href="mailto: filippo.nuccio@univ-st-etienne.fr">e-mail</a> or o
Zulip (see below for more on this).


In each lecture we will work on one file, whose solutions will be sent over by Zulip: the link below sends to a live version of the file that you can compile remotely without installing Lean, but this is a temporary solution and it is preferable to work on the project locally. For some lectures there is also a `.pdf` file with the discussed content.

Classes are on Wednesday, from 2PM to 5PM, at <a href="https://www.ens-lyon.fr/en/campus-life/campus-tour/maps-directions">ENS-Lyon</a> in the *Salle de Conseil* 
on the 3rd floor (except for the last one, that will take place on Thursday, April 3rd, **from 1.30 PM to 4.30 PM**). 
The *preliminary* schedule is as follows:

| Date      | Topic         | Accompanying file | Notes
|-----------|---------------|---------------|---------------
| Feb 19th| Introduction to proof assistants and to propositional calculus| [Lean File](https://github.com/faenuccio-teaching/GradCourse25/blob/master/GradCourse25/1_PropositionalCalculus.lean) <br> [Live Lean File](https://live.lean-lang.org/#project=mathlib-stable&codez=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) <br> [PDF](https://github.com/faenuccio-teaching/GradCourse25/blob/master/GradCourse25/1_PropositionalCalculus_lecture.pdf) |We will also address installation and practical issues.
| Feb 26th| Basic set theory and functions among sets| [Lean File](https://github.com/faenuccio-teaching/GradCourse25/blob/master/GradCourse25/2_SetsAndFunctions.lean) <br> [Live Lean File](https://live.lean-lang.org/#codez=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) <br> [PDF](https://github.com/faenuccio-teaching/GradCourse25/blob/master/GradCourse25/2_SetsAndFunctions_lecture.pdf)
| Mar 12th| Formalizing algebraic structures | [Lean File](https://github.com/faenuccio-teaching/GradCourse25/blob/master/GradCourse25/3_AlgebraicStructures.lean) <br> [Live Lean File](https://live.lean-lang.org/#project=mathlib-stable&codez=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) <br> [PDF](https://github.com/faenuccio-teaching/GradCourse25/blob/master/GradCourse25/3_AlgebraicStructures_lecture.pdf)
| Feb 19th| Formalizing topological spaces |
| Apr 3rd| Formalizing analysis and more advanced topics | | Subject to change according to participants' taste and request. <br> The class runs **from 1.30 PM to 4.30PM**



### Prerequisites 

You are required to perform the following tasks before the beginning of the course.
* Make sure that you have a working WiFi, usually via Eduroam.
* Create a <a href="https://github.com">GitHub account</a> if you do not have one yet.
* Create an account to the <a href="https://leanprover.zulipchat.com/">Lean Community Chat</a> on <a href="https://zulip.com/">Zulip</a>. You can use your 
GitHub account for that. Once you've got it, write a **D**
(irect)**M**(essage) to me 
so that I can add you to the private, dedicated channel for 
the course.
* Install a *working* `git` installation, if you do not have 
one yet: for some help, you can have a look at <a href="https://www.imo.universite-paris-saclay.fr/~patrick.massot/misc/git.html">this page maintained by Patrick Massot</a>.
* Install Lean4 on your laptop following the [official instructions](https://docs.lean-lang.org/lean4/doc/quickstart.html). You do 
not need to set-up a new Lean project, since we'll be using this repository for that. I suggest that you also install the [ErrorLens](https://marketplace.visualstudio.com/items?itemName=usernamehw.errorlens) extension to VSCode, but this is optional.
* [Fork](https://docs.github.com/en/pull-requests/collaborating-with-pull-requests/working-with-forks/fork-a-repo#forking-a-repository) the [course repository](https://github.com/faenuccio-teaching/GradCourse25.git) to your GitHub account, and then clone this fork to your laptop. The address of the repository is https://github.com/faenuccio-teaching/GradCourse25.git
* Don't panic if something went wrong: we'll try to fix problems during the first class.

