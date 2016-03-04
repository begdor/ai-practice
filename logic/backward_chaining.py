import sys
import copy
'''
class KB:
	clause = []
#MARK: 	Each clause object has:
#			a list of premises: each premise is an instance of Atomic sentence
#			one conclusion: a single Atomic sentence
#		For atomic sentence, the premise is empty(null)
#		Also, query is an instance of Clause
class Clause:
	premise = []
	conclusion = Atomic()
#MARK:	Each atomic object has:
#		predicate as String, globally unique
#		a list of Variable as arg
class Atomic:
	predicate = ''
	arg = []
#MARK:	Variable object has:
#		a list of Constant(String) as domain
class Variable:
	domain = []

def Str_to_clause(st):
	res = Clause()
	pre = st.split(' => ')[0]
	con = st.split(' => ')[1]
	# when the clause is a multiple 
	if len(con) == 0:
		for sentence in pre.split(' && '):
			res.conclusion.append(Str_to_sentence(sentence))
	# when the clause is an implication
	else:
		for sentence in pre.split(' && '):
			res.premise.append(Str_to_sentence(sentence))
		res.conclusion = toSentence(con)
	return res

def Str_to_sentence(sentence):
	senNew = Atomic()
	senNew.predicate = sentence.split('(')[0]
	for arg in sentence.split('(')[1].split(','):
		varNew = Variable()
		if arg == arg.lower():
			varNew.domain.append(arg)
		senNew.arg.append(varNew)
	arg = sentence.split('(')[1].split(')')
	varNew = Variable()
	if arg == arg.lower():
		varNew.domain.append(arg)
	senNew.arg.append(varNew)
	return senNew
'''

class KB:
	clauses = []

def Str_to_clause(st):
	res = {'premise':[],'conclusion':[]}
	pre = st.split(' => ')[0]
	con = ''
	if len(st.split(' => ')) == 2:
		con = st.split(' => ')[1]
	# when the clause is a multiple 
	if len(con) == 0:
		for sentence in pre.split(' && '):
			res['conclusion'].append(Str_to_sentence(sentence))
	# when the clause is an implication
	else:
		for sentence in pre.split(' && '):
			res['premise'].append(Str_to_sentence(sentence))
		res['conclusion'].append(Str_to_sentence(con))
	return res

def Str_to_sentence(sentence):
	res = {'arg':[]}
	res['predicate'] = sentence.split('(')[0]
	for arg in sentence.split('(')[1].split(','):
		res['arg'].append(arg)
		last = arg
	arg = last.split(')')[0]
	res['arg'][len(res['arg'])-1] = arg
	return res

#	Unitfication
#=================================================

# considered that in this homework,  the query(goal) would be 
#	1) single atomic 
#	2) multiple atomic in CNF
#	3) single predicate with one unknown variable
#	only the case 3) need to call Unify(), so that in Unify() we don't need to consider compund
def Unify(x,y,theta):
	print 'Inside the Unify'
	if theta is None:
		return None
	elif x == y:
		return theta
	elif not isinstance(x,list) and x == x.lower():
		return Unify_var(x,y,theta)
	elif not isinstance(x,list) and y == y.lower():
		return Unify_var(y,x,theta)
	elif isinstance(x,list) and isinstance(y,list) and len(x) == len(y):
		if len(x) == 0: 
			return theta
		return Unify(x[1:],y[1:],Unify(x[0],y[0],theta))
	else: return None

def Unify_var(var,x,theta):
	print 'Inside the Unify_var'
	if var in theta:
		return Unify(theta[var], x, theta)
	elif x == x.lower():
		if x in theta:
			return Unify(var,theta[x],theta)
	#TODO:	add occur_check and return None
	else:
		thetaNew = theta.copy()
		thetaNew[var] = x
		return thetaNew


#	Fetch rule for goals
#=================================================
def Fetch_rules(KB,goal):
	print 'Inside the Fetch_rules'
	res = []
	for clause in KB.clauses:
		if len(clause['conclusion']) == 0:
			pass
		else:
			for sentence in goal['conclusion']:
				# in this homework, each conclusion only has one sentence
				if clause['conclusion'][0]['predicate'] == sentence['predicate']:
					if clause['conclusion'][0]['arg'] == sentence['arg']:
						print sentence['arg']
					res.append(clause)
	return res
#	Backward Chaining
#=================================================
def Fol_bc_ask(KB,query):
	print 'Inside the Fol_bc_ask'
	return Fol_bc_or(KB,query,{})

# travse the KB, return a list of clauses(rules) that has goal as their conclusion


def Fol_bc_or(KB,goal,theta):
	print 'Inside the Fol_bc_or'
	for rule in Fetch_rules(KB,goal):
		lhs = rule['premise']
		#TODO:	standardize-variables
		# 		exclude the case that goal is multi atomic
		if len(lhs) == 0:
			rhs = rule['conclusion']
			pass
		else:
			rhs = rule['conclusion'][0]
			'''
			print 'what is in this rule: rhs,goal,theta'
			print rhs['arg']
			print goal['conclusion'][0]['arg']
			print Unify(rhs['arg'],goal['conclusion'][0]['arg'],theta)	
			print '------------------'
			'''
			print 'and:lhs'
			print lhs
			for thetaR in Fol_bc_and(KB,lhs,Unify(rhs['arg'],goal['conclusion'][0]['arg'],theta)):
				print 'thetaR'
				print thetaR
				yield thetaR

			print 'endof and'

def Fol_bc_and(KB,goals,theta):
	print 'Inside the Fol_bc_and'
	if theta is None: 
		pass
	elif len(goals) == 0: #	if the query is single/multiple atomic sentence, lhs would be None	
		yield theta
	else:
		first, rest = goals[0], goals[1:]
		print 'first'
		print theta
		for theta1 in Fol_bc_or(KB, subst(theta, first), theta):
			for theta2 in Fol_bc_and(KB, rest, theta1):
				print 'theta2'
				print theta2
				yield theta2

def subst(theta, sentence):
	print 'Inside the subst'
	res = {'premise':[],'conclusion':[]}
	senNew = sentence.copy()
	for arg in theta:
		for i in range(len(senNew['arg'])):
			if senNew['arg'][i] == arg:
				senNew['arg'][i] = theta[arg]
	res['conclusion'].append(senNew)
	print res
	return res


#	Read input
#=================================================
if sys.argv[1]!= '-i':
	print 'Invalid command.\n'
	print 'Please follow the syntax:\n'
	print '"python <Script Name> -i <Input Path>\n'
path = sys.argv[2]

file = open(path,'r')
count = 0
num = 0
kb = KB()
for line in file:
	line = line.strip('\n')
	if count == 1:
		num = int(line)
		break
	query = Str_to_clause(line)
	count += 1
count = 0
for line in file:
	line = line.strip('\n')
	kb.clauses.append(Str_to_clause(line))
	count += 1
	if count == num:
		break

ans = Fol_bc_ask(kb,query)
res = []
for a in ans:	
	res.append(a)
print res