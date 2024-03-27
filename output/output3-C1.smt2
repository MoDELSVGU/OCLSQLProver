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
(declare-const self Classifier)
(assert (Student self))
; Student.allInstances()->forAll(s| not s.age.oclIsUndefined())
(assert (forall ((s Classifier)) (and (=> (Student s) (not (or (= (age_Student s) nullInt) (or (= s nullClassifier) (= s invalidClassifier))))) (not false))))
; Lecturer.allInstances()->forAll(l| not l.age.oclIsUndefined())
(assert (forall ((l Classifier)) (and (=> (Lecturer l) (not (or (= (age_Lecturer l) nullInt) (or (= l nullClassifier) (= l invalidClassifier))))) (not false))))
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
(declare-fun index0 (Int) Bool) ; index0 = [Select]: SELECT NOT EXISTS (SELECT 1 FROM (SELECT s.age, e.lecturers FROM Student AS s JOIN Enrolment AS e ON e.students = s.Student_id) AS temp JOIN Lecturer AS l WHERE temp.age >= l.age AND l.Lecturer_id = temp.lecturers)
(declare-fun index1 (Int) Bool) ; index1 = [Select]: SELECT 1 FROM (SELECT s.age, e.lecturers FROM Student AS s JOIN Enrolment AS e ON e.students = s.Student_id) AS temp JOIN Lecturer AS l WHERE temp.age >= l.age AND l.Lecturer_id = temp.lecturers
(declare-fun index2 (Int) Bool) ; index2 = [Select]: SELECT s.age, e.lecturers FROM Student AS s JOIN Enrolment AS e ON e.students = s.Student_id
(declare-fun index3 (Int) Bool) ; index3 = [Join]: Student <--> Enrolment
(declare-fun index4 (Int) Bool) ; index4 = [Join]: 2 <--> Lecturer
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
(declare-fun val-index3-expr0 (Int) Classifier) ; val-index3-expr0 = e.students
(declare-fun val-index3-expr1 (Int) Classifier) ; val-index3-expr1 = s.Student_id
(declare-fun val-index3-expr2 (Int) BOOL) ; val-index3-expr2 = e.students = s.Student_id
(declare-fun val-index2-expr3 (Int) Int) ; val-index2-expr3 = s.age
(declare-fun val-index2-expr4 (Int) Classifier) ; val-index2-expr4 = e.lecturers
(declare-fun val-index4-expr5 (Int) Int) ; val-index4-expr5 = temp.age
(declare-fun val-index4-expr6 (Int) Int) ; val-index4-expr6 = l.age
(declare-fun val-index4-expr7 (Int) BOOL) ; val-index4-expr7 = temp.age >= l.age
(declare-fun val-index4-expr8 (Int) Classifier) ; val-index4-expr8 = l.Lecturer_id
(declare-fun val-index4-expr9 (Int) Classifier) ; val-index4-expr9 = temp.lecturers
(declare-fun val-index4-expr10 (Int) BOOL) ; val-index4-expr10 = l.Lecturer_id = temp.lecturers
(declare-fun val-index4-expr11 (Int) BOOL) ; val-index4-expr11 = temp.age >= l.age AND l.Lecturer_id = temp.lecturers
(declare-fun val-index1-expr12 (Int) Int) ; val-index1-expr12 = 1
(declare-fun val-index0-expr13 (Int) Int) ; val-index0-expr13 = (SELECT 1 FROM (SELECT s.age, e.lecturers FROM Student AS s JOIN Enrolment AS e ON e.students = s.Student_id) AS temp JOIN Lecturer AS l WHERE temp.age >= l.age AND l.Lecturer_id = temp.lecturers)
(declare-fun val-index0-expr14 (Int) BOOL) ; val-index0-expr14 = EXISTS (SELECT 1 FROM (SELECT s.age, e.lecturers FROM Student AS s JOIN Enrolment AS e ON e.students = s.Student_id) AS temp JOIN Lecturer AS l WHERE temp.age >= l.age AND l.Lecturer_id = temp.lecturers)
(declare-fun val-index0-res (Int) BOOL) ; val-index0-res = NOT EXISTS (SELECT 1 FROM (SELECT s.age, e.lecturers FROM Student AS s JOIN Enrolment AS e ON e.students = s.Student_id) AS temp JOIN Lecturer AS l WHERE temp.age >= l.age AND l.Lecturer_id = temp.lecturers)
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
(assert (exists ((x Int)) (and (index0 x) (forall ((y Int)) (=> (not (= x y)) (not (index0 y)))))))
(assert (forall ((x Int)) (= (index1 x) (and (index4 x) (= (val-index4-expr11 x) TRUE)))))
(assert (forall ((x Int)) (= (index2 x) (and (index3 x) (= (val-index3-expr2 x) TRUE)))))
(assert (forall ((x Int) (y Int)) (=> (and (index3 x) (index3 y) (not (= x y))) (not (and (= (left x) (left y)) (= (right x) (right y)))))))
(assert (forall ((x Int) (y Int)) (=> (indexStudent x) (indexEnrolment y) (exists ((z Int)) (and (index3 z) (= x (left z)) (= y (right z)))))))
(assert (forall ((z Int)) (=> (index3 z) (exists ((x Int) (y Int)) (and (indexStudent x) (indexEnrolment y) (= x (left z)) (= y (right z)))))))
(assert (forall ((x Int) (y Int)) (=> (and (index4 x) (index4 y) (not (= x y))) (not (and (= (left x) (left y)) (= (right x) (right y)))))))
(assert (forall ((x Int) (y Int)) (=> (index2 x) (indexLecturer y) (exists ((z Int)) (and (index4 z) (= x (left z)) (= y (right z)))))))
(assert (forall ((z Int)) (=> (index4 z) (exists ((x Int) (y Int)) (and (index2 x) (indexLecturer y) (= x (left z)) (= y (right z)))))))
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
(assert (forall ((x Int)) (=> (index3 x) (= (val-index3-expr0 x) (val-indexEnrolment-students (right x))))))
(assert (forall ((x Int)) (=> (index3 x) (= (val-index3-expr1 x) (val-indexStudent-Student_id (left x))))))
(assert (forall ((x Int)) (=> (index3 x) (= (= (val-index3-expr2 x) TRUE) (and (not (= (val-index3-expr0 x) nullClassifier)) (not (= (val-index3-expr1 x) nullClassifier)) (= (val-index3-expr0 x) (val-index3-expr1 x)))))))
(assert (forall ((x Int)) (=> (index3 x) (= (= (val-index3-expr2 x) FALSE) (and (not (= (val-index3-expr0 x) nullClassifier)) (not (= (val-index3-expr1 x) nullClassifier)) (not (= (val-index3-expr0 x) (val-index3-expr1 x))))))))
(assert (forall ((x Int)) (=> (index3 x) (= (= (val-index3-expr2 x) NULL) (or (= (val-index3-expr0 x) nullClassifier) (= (val-index3-expr1 x) nullClassifier))))))
(assert (forall ((x Int)) (=> (index2 x) (= (val-index2-expr3 x) (val-indexStudent-age (left x))))))
(assert (forall ((x Int)) (=> (index2 x) (= (val-index2-expr4 x) (val-indexEnrolment-lecturers (right x))))))
(assert (forall ((x Int)) (=> (index4 x) (= (val-index4-expr5 x) (val-index2-expr3 (left x))))))
(assert (forall ((x Int)) (=> (index4 x) (= (val-index4-expr6 x) (val-indexLecturer-age (right x))))))
(assert (forall ((x Int)) (=> (index4 x) (= (= (val-index4-expr7 x) TRUE) (and (not (= (val-index4-expr5 x) nullInt)) (not (= (val-index4-expr6 x) nullInt)) (>= (val-index4-expr5 x) (val-index4-expr6 x)))))))
(assert (forall ((x Int)) (=> (index4 x) (= (= (val-index4-expr7 x) FALSE) (and (not (= (val-index4-expr5 x) nullInt)) (not (= (val-index4-expr6 x) nullInt)) (not (>= (val-index4-expr5 x) (val-index4-expr6 x))))))))
(assert (forall ((x Int)) (=> (index4 x) (= (= (val-index4-expr7 x) NULL) (or (= (val-index4-expr5 x) nullInt) (= (val-index4-expr6 x) nullInt))))))
(assert (forall ((x Int)) (=> (index4 x) (= (val-index4-expr8 x) (val-indexLecturer-Lecturer_id (right x))))))
(assert (forall ((x Int)) (=> (index4 x) (= (val-index4-expr9 x) (val-index2-expr4 (left x))))))
(assert (forall ((x Int)) (=> (index4 x) (= (= (val-index4-expr10 x) TRUE) (and (not (= (val-index4-expr8 x) nullClassifier)) (not (= (val-index4-expr9 x) nullClassifier)) (= (val-index4-expr8 x) (val-index4-expr9 x)))))))
(assert (forall ((x Int)) (=> (index4 x) (= (= (val-index4-expr10 x) FALSE) (and (not (= (val-index4-expr8 x) nullClassifier)) (not (= (val-index4-expr9 x) nullClassifier)) (not (= (val-index4-expr8 x) (val-index4-expr9 x))))))))
(assert (forall ((x Int)) (=> (index4 x) (= (= (val-index4-expr10 x) NULL) (or (= (val-index4-expr8 x) nullClassifier) (= (val-index4-expr9 x) nullClassifier))))))
(assert (forall ((x Int)) (=> (index4 x) (= (= (val-index4-expr11 x) TRUE) (and (= (val-index4-expr7 x) TRUE) (= (val-index4-expr10 x) TRUE))))))
(assert (forall ((x Int)) (=> (index4 x) (= (= (val-index4-expr11 x) FALSE) (or (= (val-index4-expr7 x) FALSE) (= (val-index4-expr10 x) FALSE))))))
(assert (forall ((x Int)) (=> (index4 x) (= (= (val-index4-expr11 x) NULL) (or (and (= (val-index4-expr7 x) NULL) (= (val-index4-expr10 x) TRUE)) (and (= (val-index4-expr7 x) TRUE) (= (val-index4-expr10 x) NULL)) (and (= (val-index4-expr7 x) NULL) (= (val-index4-expr10 x) NULL)))))))
(assert (forall ((x Int)) (=> (index1 x) (= (val-index1-expr12 x) 1))))
(assert (not (= 1 nullInt)))
(assert (not (= 1 invalidInt)))
; In this case, the val of the subselect is irrelevant to the decidability of the theory
; ergo, it is omitted here for the sake of simplicity
(assert (forall ((x Int)) (=> (index0 x) (= (= (val-index0-expr14 x) TRUE) (exists ((y Int)) (index1 y))))))
(assert (forall ((x Int)) (=> (index0 x) (= (= (val-index0-expr14 x) FALSE) (not (exists ((y Int)) (index1 y)))))))
(assert (forall ((x Int)) (=> (index0 x) (= (= (val-index0-res x) TRUE) (= (val-index0-expr14 x) FALSE)))))
(assert (forall ((x Int)) (=> (index0 x) (= (= (val-index0-res x) FALSE) (= (val-index0-expr14 x) TRUE)))))
(assert (forall ((x Int)) (=> (index0 x) (= (= (val-index0-res x) NULL) (= (val-index0-expr14 x) NULL)))))
(assert (not (exists ((x Int)) (and (index0 x) (forall ((y Int)) (=> (not (= x y)) (not (index0 y))))))))
(check-sat)