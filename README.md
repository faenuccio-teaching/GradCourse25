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


In each lecture we will work on one file, to which I post solutions some time after the lecture: the link below sends to a live version of the file that you can compile remotely without installing Lean, but this is a temporary solution and it is preferable to work on the project locally. For some lectures there are also a `.md` and a `.pdf` file with the discussed content. If you add the [markdown-collapsible](https://marketplace.visualstudio.com/items?itemName=zinc0x1E.markdown-collapsible) extension to your VSCode you can expand the `▸` symbols as I do in class.

Classes are on Wednesday, from 2PM to 5PM, at <a href="https://www.ens-lyon.fr/en/campus-life/campus-tour/maps-directions">ENS-Lyon</a> in the *Salle de Conseil* 
on the 3rd floor (except for the last one, that will take place in another room in the 
same floor). 
The *preliminary* schedule is as follows:

| Date      | Topic         | Accompanying file | Notes
|-----------|---------------|---------------|---------------
| Feb 19th| Introduction to proof assistants and to propositional calculus| [Lean File](https://live.lean-lang.org/#codez=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) <br> [MarkDown](https://github.com/faenuccio-teaching/GradCourse25/blob/master/GradCourse25/1_PropositionalCalculus_lecture.md) <br> [PDF](https://github.com/faenuccio-teaching/GradCourse25/blob/master/GradCourse25/1_PropositionalCalculus_lecture.pdf) <br> Solutions |We will also address installation and practical issues.
| Feb 26th| Basic set theory and functions among sets|
| Mar 12th| Formalizing algebraic structures |
| Feb 19th| Formalizing topological spaces |
| Feb 26th| Formalizing analysis and more advanced topics | | Subject to change according to participants' taste and request.



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

