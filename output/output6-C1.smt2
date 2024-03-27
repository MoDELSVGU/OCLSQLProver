;*************************************************************************
; Copyright 2022
; 
; Licensed under the Apache License, Version 2.0 (the "License"); you may not
; use this file except in compliance with the License. You may obtain a copy of
; the License at
; 
; http://www.apache.org/licenses/LICENSE-2.0
; 
; Unless required by applicable law or agreed to in writing, software
; distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
; WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
; License for the specific language governing permissions and limitations under
; the License.
; 
; @author: Anonymous Author(s)
;**************************************************************************/
(set-option :produce-models true)
(declare-sort Classifier 0)
(declare-sort Type 0)
(declare-const nullClassifier Classifier)
(declare-const invalidClassifier Classifier)
(declare-const nullInt Int)
(declare-const invalidInt Int)
(declare-const nullString String)
(declare-const invalidString String)
(assert (distinct nullClassifier invalidClassifier))
(assert (distinct nullInt invalidInt))
(assert (distinct nullString invalidString))
(declare-fun OclIsTypeOf (Classifier Type) Bool)
(declare-fun OclIsKindOf (Classifier Type) Bool)
(declare-fun Lecturer (Classifier) Bool)
(assert (not (Lecturer nullClassifier)))
(declare-const LecturerType Type)
(declare-fun Student (Classifier) Bool)
(assert (not (Student nullClassifier)))
(declare-const StudentType Type)
(assert (not (Lecturer invalidClassifier)))
(declare-fun email_Lecturer (Classifier) String)
(assert (= (email_Lecturer nullClassifier) invalidString))
(assert (= (email_Lecturer invalidClassifier) invalidString))
(assert (forall ((x Classifier))
    (=> (Lecturer x)
        (distinct (email_Lecturer x) invalidString))))
(declare-fun age_Lecturer (Classifier) Int)
(assert (= (age_Lecturer nullClassifier) invalidInt))
(assert (= (age_Lecturer invalidClassifier) invalidInt))
(assert (forall ((x Classifier))
    (=> (Lecturer x)
        (distinct (age_Lecturer x) invalidInt))))
(declare-fun name_Lecturer (Classifier) String)
(assert (= (name_Lecturer nullClassifier) invalidString))
(assert (= (name_Lecturer invalidClassifier) invalidString))
(assert (forall ((x Classifier))
    (=> (Lecturer x)
        (distinct (name_Lecturer x) invalidString))))
(assert (distinct LecturerType StudentType))
(assert (forall ((x Classifier))
    (and (=> (Lecturer x)
             (OclIsTypeOf x LecturerType))
         (=> (OclIsTypeOf x LecturerType)
             (Lecturer x)))))
(assert (forall ((x Classifier))
    (and (=> (Lecturer x)
             (OclIsKindOf x LecturerType))
         (=> (OclIsKindOf x LecturerType)
             (Lecturer x)))))
(assert (not (Student invalidClassifier)))
(declare-fun age_Student (Classifier) Int)
(assert (= (age_Student nullClassifier) invalidInt))
(assert (= (age_Student invalidClassifier) invalidInt))
(assert (forall ((x Classifier))
    (=> (Student x)
        (distinct (age_Student x) invalidInt))))
(declare-fun email_Student (Classifier) String)
(assert (= (email_Student nullClassifier) invalidString))
(assert (= (email_Student invalidClassifier) invalidString))
(assert (forall ((x Classifier))
    (=> (Student x)
        (distinct (email_Student x) invalidString))))
(declare-fun name_Student (Classifier) String)
(assert (= (name_Student nullClassifier) invalidString))
(assert (= (name_Student invalidClassifier) invalidString))
(assert (forall ((x Classifier))
    (=> (Student x)
        (distinct (name_Student x) invalidString))))
(assert (distinct StudentType LecturerType))
(assert (forall ((x Classifier))
    (and (=> (Student x)
             (OclIsTypeOf x StudentType))
         (=> (OclIsTypeOf x StudentType)
             (Student x)))))
(assert (forall ((x Classifier))
    (and (=> (Student x)
             (OclIsKindOf x StudentType))
         (=> (OclIsKindOf x StudentType)
             (Student x)))))
(declare-fun Enrolment (Classifier Classifier) Bool)
(assert (forall ((x Classifier))
    (forall ((y Classifier)) 
        (=> (Enrolment x y) 
            (and (Lecturer x) (Student y))))))
(assert (forall ((x Classifier)) 
    (=> (Lecturer x) (not (Student x)))))
(assert (forall ((x Classifier)) 
    (=> (Student x) (not (Lecturer x)))))
(declare-const user String)
(declare-const self Classifier)
(assert (Student self))
; Student.allInstances()->forAll(s|not s.age.oclIsUndefined())
(assert (forall ((s Classifier)) (and (=> (Student s) (not (or (= (age_Student s) nullInt) (or (= s nullClassifier) (= s invalidClassifier))))) (not false))))
; not user.oclIsUndefined()
(assert (not (or (= user nullString) (= user invalidString))))
(declare-sort BOOL 0)
(declare-const TRUE BOOL)
(declare-const FALSE BOOL)
(declare-const NULL BOOL)
(assert (not (= TRUE FALSE)))
(assert (not (= TRUE NULL)))
(assert (not (= FALSE NULL)))
(assert (forall ((x BOOL)) (or (= x TRUE) (or (= x FALSE) (= x NULL)))))
(declare-fun id (Int) Classifier)
(declare-fun left (Int) Int)
(declare-fun right (Int) Int)
(declare-fun indexLecturer (Int) Bool) ; indexLecturer = [Entity]: Lecturer
(declare-fun indexStudent (Int) Bool) ; indexStudent = [Entity]: Student
(declare-fun indexEnrolment (Int) Bool) ; indexEnrolment = [Association]: Enrolment
(declare-fun index0 (Int) Bool) ; index0 = [Select]: SELECT CASE WHEN s.name IS NULL THEN user IS NULL ELSE CASE WHEN user IS NULL THEN FALSE ELSE s.name = user END END FROM Student AS s WHERE s.Student_id = self
(declare-fun val-indexLecturer-email (Int) String) ; val-indexLecturer-email = email
(declare-fun val-indexLecturer-name (Int) String) ; val-indexLecturer-name = name
(declare-fun val-indexLecturer-age (Int) Int) ; val-indexLecturer-age = age
(declare-fun val-indexLecturer-Lecturer_id (Int) Classifier) ; val-indexLecturer-Lecturer_id = Lecturer_id
(declare-fun val-indexStudent-email (Int) String) ; val-indexStudent-email = email
(declare-fun val-indexStudent-age (Int) Int) ; val-indexStudent-age = age
(declare-fun val-indexStudent-name (Int) String) ; val-indexStudent-name = name
(declare-fun val-indexStudent-Student_id (Int) Classifier) ; val-indexStudent-Student_id = Student_id
(declare-fun val-indexEnrolment-students (Int) Classifier) ; val-indexEnrolment-students = students
(declare-fun val-indexEnrolment-lecturers (Int) Classifier) ; val-indexEnrolment-lecturers = lecturers
(declare-fun val-indexStudent-expr0 (Int) Classifier) ; val-indexStudent-expr0 = s.Student_id
(declare-fun val-indexStudent-expr1 (Int) Classifier) ; val-indexStudent-expr1 = self
(declare-fun val-indexStudent-expr2 (Int) BOOL) ; val-indexStudent-expr2 = s.Student_id = self
(declare-fun val-index0-expr3 (Int) String) ; val-index0-expr3 = s.name
(declare-fun val-index0-expr4 (Int) BOOL) ; val-index0-expr4 = s.name IS NULL
(declare-fun val-index0-expr5 (Int) String) ; val-index0-expr5 = user
(declare-fun val-index0-expr6 (Int) BOOL) ; val-index0-expr6 = user IS NULL
(declare-fun val-index0-expr7 (Int) String) ; val-index0-expr7 = user
(declare-fun val-index0-expr8 (Int) BOOL) ; val-index0-expr8 = user IS NULL
(declare-fun val-index0-expr9 (Int) BOOL) ; val-index0-expr9 = FALSE
(declare-fun val-index0-expr10 (Int) String) ; val-index0-expr10 = s.name
(declare-fun val-index0-expr11 (Int) String) ; val-index0-expr11 = user
(declare-fun val-index0-expr12 (Int) BOOL) ; val-index0-expr12 = s.name = user
(declare-fun val-index0-expr13 (Int) BOOL) ; val-index0-expr13 = CASE WHEN user IS NULL THEN FALSE ELSE s.name = user END
(declare-fun val-index0-res (Int) BOOL) ; val-index0-res = CASE WHEN s.name IS NULL THEN user IS NULL ELSE CASE WHEN user IS NULL THEN FALSE ELSE s.name = user END END
(assert (forall ((x Int)) (=> (indexLecturer x) (exists ((c Classifier)) (and (Lecturer c) (= c (id x)))))))
(assert (forall ((c Classifier)) (=> (Lecturer c) (exists ((x Int)) (and (indexLecturer x) (= c (id x)))))))
(assert (forall ((x Int) (y Int)) (=> (and (indexLecturer x) (indexLecturer y) (not (= x y))) (not (= (id x) (id y))))))
(assert (forall ((x Int)) (=> (indexLecturer x) (= (val-indexLecturer-Lecturer_id x) (id x)))))
(assert (forall ((x Int)) (=> (indexStudent x) (exists ((c Classifier)) (and (Student c) (= c (id x)))))))
(assert (forall ((c Classifier)) (=> (Student c) (exists ((x Int)) (and (indexStudent x) (= c (id x)))))))
(assert (forall ((x Int) (y Int)) (=> (and (indexStudent x) (indexStudent y) (not (= x y))) (not (= (id x) (id y))))))
(assert (forall ((x Int)) (=> (indexStudent x) (= (val-indexStudent-Student_id x) (id x)))))
(assert (forall ((x Int) (y Int)) (=> (and (indexEnrolment x) (indexEnrolment y) (not (= x y))) (not (and (= (left x) (left y)) (= (right x) (right y)))))))
(assert (forall ((x Classifier) (y Classifier)) (=> (Enrolment x y) (exists ((z Int)) (and (indexEnrolment z) (= x (id (left z))) (= y (id (right z))))))))
(assert (forall ((z Int)) (=> (indexEnrolment z) (exists ((x Classifier) (y Classifier)) (and (Enrolment x y) (= x (id (left z))) (= y (id (right z))))))))
(assert (forall ((x Int)) (= (index0 x) (and (indexStudent x) (= (val-indexStudent-expr2 x) TRUE)))))
(assert (forall ((x Int)) (=> (indexLecturer x) (= (val-indexLecturer-email x) (email_Lecturer (id x))))))
(assert (forall ((x Int)) (=> (indexLecturer x) (= (val-indexLecturer-name x) (name_Lecturer (id x))))))
(assert (forall ((x Int)) (=> (indexLecturer x) (= (val-indexLecturer-age x) (age_Lecturer (id x))))))
(assert (forall ((x Int)) (=> (indexLecturer x) (= (val-indexLecturer-Lecturer_id x) (id x)))))
(assert (forall ((x Int)) (=> (indexStudent x) (= (val-indexStudent-email x) (email_Student (id x))))))
(assert (forall ((x Int)) (=> (indexStudent x) (= (val-indexStudent-age x) (age_Student (id x))))))
(assert (forall ((x Int)) (=> (indexStudent x) (= (val-indexStudent-name x) (name_Student (id x))))))
(assert (forall ((x Int)) (=> (indexStudent x) (= (val-indexStudent-Student_id x) (id x)))))
(assert (forall ((x Int)) (=> (indexEnrolment x) (= (val-indexEnrolment-students x) (id (right x))))))
(assert (forall ((x Int)) (=> (indexEnrolment x) (= (val-indexEnrolment-lecturers x) (id (left x))))))
(assert (forall ((x Int)) (=> (indexStudent x) (= (val-indexStudent-expr0 x) (val-indexStudent-Student_id x)))))
(assert (forall ((x Int)) (=> (indexStudent x) (= (val-indexStudent-expr1 x) self))))
(assert (forall ((x Int)) (=> (indexStudent x) (= (= (val-indexStudent-expr2 x) TRUE) (and (not (= (val-indexStudent-expr0 x) nullClassifier)) (not (= (val-indexStudent-expr1 x) nullClassifier)) (= (val-indexStudent-expr0 x) (val-indexStudent-expr1 x)))))))
(assert (forall ((x Int)) (=> (indexStudent x) (= (= (val-indexStudent-expr2 x) FALSE) (and (not (= (val-indexStudent-expr0 x) nullClassifier)) (not (= (val-indexStudent-expr1 x) nullClassifier)) (not (= (val-indexStudent-expr0 x) (val-indexStudent-expr1 x))))))))
(assert (forall ((x Int)) (=> (indexStudent x) (= (= (val-indexStudent-expr2 x) NULL) (or (= (val-indexStudent-expr0 x) nullClassifier) (= (val-indexStudent-expr1 x) nullClassifier))))))
(assert (forall ((x Int)) (=> (index0 x) (= (val-index0-expr3 x) (val-indexStudent-name x)))))
(assert (forall ((x Int)) (=> (index0 x) (= (= (val-index0-expr4 x) TRUE) (= (val-index0-expr3 x) nullString)))))
(assert (forall ((x Int)) (=> (index0 x) (= (= (val-index0-expr4 x) FALSE) (not (= (val-index0-expr3 x) nullString))))))
(assert (forall ((x Int)) (=> (index0 x) (= (val-index0-expr5 x) user))))
(assert (forall ((x Int)) (=> (index0 x) (= (= (val-index0-expr6 x) TRUE) (= (val-index0-expr5 x) nullString)))))
(assert (forall ((x Int)) (=> (index0 x) (= (= (val-index0-expr6 x) FALSE) (not (= (val-index0-expr5 x) nullString))))))
(assert (forall ((x Int)) (=> (index0 x) (= (val-index0-expr7 x) user))))
(assert (forall ((x Int)) (=> (index0 x) (= (= (val-index0-expr8 x) TRUE) (= (val-index0-expr7 x) nullString)))))
(assert (forall ((x Int)) (=> (index0 x) (= (= (val-index0-expr8 x) FALSE) (not (= (val-index0-expr7 x) nullString))))))
(assert (forall ((x Int)) (=> (index0 x) (= (val-index0-expr9 x) FALSE))))
(assert (forall ((x Int)) (=> (index0 x) (= (val-index0-expr10 x) (val-indexStudent-name x)))))
(assert (forall ((x Int)) (=> (index0 x) (= (val-index0-expr11 x) user))))
(assert (forall ((x Int)) (=> (index0 x) (= (= (val-index0-expr12 x) TRUE) (and (not (= (val-index0-expr10 x) nullString)) (not (= (val-index0-expr11 x) nullString)) (= (val-index0-expr10 x) (val-index0-expr11 x)))))))
(assert (forall ((x Int)) (=> (index0 x) (= (= (val-index0-expr12 x) FALSE) (and (not (= (val-index0-expr10 x) nullString)) (not (= (val-index0-expr11 x) nullString)) (not (= (val-index0-expr10 x) (val-index0-expr11 x))))))))
(assert (forall ((x Int)) (=> (index0 x) (= (= (val-index0-expr12 x) NULL) (or (= (val-index0-expr10 x) nullString) (= (val-index0-expr11 x) nullString))))))
(assert (forall ((x Int)) (=> (index0 x) (= (= (val-index0-expr13 x) (val-index0-expr9 x)) (= (val-index0-expr8 x) TRUE)))))
(assert (forall ((x Int)) (=> (index0 x) (= (= (val-index0-expr13 x) (val-index0-expr12 x)) (or (= (val-index0-expr8 x) FALSE) (= (val-index0-expr8 x) NULL))))))
(assert (forall ((x Int)) (=> (index0 x) (= (= (val-index0-res x) (val-index0-expr6 x)) (= (val-index0-expr4 x) TRUE)))))
(assert (forall ((x Int)) (=> (index0 x) (= (= (val-index0-res x) (val-index0-expr13 x)) (or (= (val-index0-expr4 x) FALSE) (= (val-index0-expr4 x) NULL))))))
(assert (not (exists ((x Int)) (and (index0 x) (forall ((y Int)) (=> (not (= x y)) (not (index0 y))))))))
(check-sat)