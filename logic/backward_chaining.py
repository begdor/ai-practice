import sys
import copy

class KB:
	clauses = []

def Str_to_clause(st,count):
	res = {'premise':[],'conclusion':[]}
	pre = st.split(' => ')[0]
	con = ''
	if len(st.split(' => ')) == 2:
		con = st.split(' => ')[1]
	# when the clause is a multiple 
	if len(con) == 0:
		for sentence in pre.split(' && '):
			res['conclusion'].append(Str_to_sentence(sentence,count))
	# when the clause is an implication
	else:
		for sentence in pre.split(' && '):
			res['premise'].append(Str_to_sentence(sentence,count))
		res['conclusion'].append(Str_to_sentence(con,count))
	return res

def Str_to_sentence(sentence,count):
	res = {'arg':[]}
	res['predicate'] = sentence.split('(')[0]
	for arg in sentence.split('(')[1].split(', '):
		if arg == arg.lower():
			arg += str(count)
		res['arg'].append(arg)
		last = arg
	arg = last.split(')')[0]
	if arg == arg.lower():
		arg += str(count)
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
	elif x == x.lower() and x in theta:
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
			# in this homework, int KB, each conclusion only has one sentence
			if clause['conclusion'][0]['predicate'] == goal['predicate']:
				res.append(clause)
	return res

def Standardize(rule):
	global standCount
	ruleNew = copy.deepcopy(rule)
	for i in range(0,len(ruleNew['premise'])):
		for j in range(0,len(ruleNew['premise'][i]['arg'])):
			if ruleNew['premise'][i]['arg'][j] == ruleNew['premise'][i]['arg'][j].lower():
				ruleNew['premise'][i]['arg'][j] += standCount
	for i in range(0,len(ruleNew['conclusion'])):
		for j in range(0,len(ruleNew['conclusion'][i]['arg'])):
			if ruleNew['conclusion'][i]['arg'][j] == ruleNew['conclusion'][i]['arg'][j].lower():
				ruleNew['conclusion'][i]['arg'][j] += standCount
	standCount = chr(ord(standCount)+1)
	return ruleNew

#	Backward Chaining
#=================================================
def Fol_bc_ask(KB,query):
	print 'inside Fol_bc_ask'
	for theta in Fol_bc_or(kb, query, {}):
		if theta is None:
			string = 'False: ' + query['predicate']+'('
			for arg in query['arg']:
				string += arg + ', '
			strFal = string[:(len(string)-2)] + ')'
			output.write(strFal)
			output.write('\n')
			return False
	return True

# travse the KB, return a list of clauses(rules) that has goal as their conclusion


def Fol_bc_or(KB,goal,theta):
	print 'Inside the Fol_bc_or'
	senNew = subst(theta,goal) 
	
	string = 'Ask: '+senNew['predicate']+'('
	for arg in senNew['arg']:
		if arg == arg.lower():
			string += '_, '
		else:
			string += arg + ', '
	strAsk = string[:(len(string)-2)] + ')'

	rules = []
	for rule in Fetch_rules(KB,goal):
		ruleNew = Standardize(rule)
		lhs = ruleNew['premise']
		rh_list = ruleNew['conclusion']
		#TODO:	standardize-variables
		# 		exclude the case that goal is multi atomic

		for rhs in rh_list:
			thetaUni = Unify(rhs['arg'],goal['arg'],theta)
			#if the goal match the rule, => True + sentence
			if thetaUni is None:
				pass
			else:
				rules.append(ruleNew)
	if len(rules) == 0:


		print '~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~'
		print strAsk
		output.write(strAsk)
		output.write('\n')
		print '~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~'

		string = 'False: ' + senNew['predicate']+'('
		for arg in senNew['arg']:
			string += arg + ', '
		strFal = string[:(len(string)-2)] + ')'
		print '~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~'
		print strFal
		output.write(strFal)
		output.write('\n')
		print '~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~'
	for rule in rules:
		lhs = rule['premise']
		rh_list = rule['conclusion']
		for rhs in rh_list:
			thetaUni = Unify(rhs['arg'],goal['arg'],theta)
			print '~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~'
			print strAsk
			output.write(strAsk)
			output.write('\n')
			print '~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~'
			for thetaR in Fol_bc_and(KB,lhs,thetaUni):

				string = 'True: ' + goal['predicate']+'('
				for arg in subst(thetaR,goal)['arg']:
					string += arg + ', '
				strTrue = string[:(len(string)-2)] + ')'
				print '~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~'
				print strTrue
				output.write(strTrue)
				output.write('\n')
				print '~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~'
				for i in range(0,len(query['conclusion'])):
					if query['conclusion'][i]['predicate'] == goal['predicate']:
						isTrue = True
						for j in range(0,len(goal['arg'])):
							if query['conclusion'][i]['arg'][j] == query['conclusion'][i]['arg'][j].lower():
								continue
							else:
								each = goal['arg'][j]
								isTrue = isTrue and each != each.lower() and query['conclusion'][i]['arg'][j] == each
						if isTrue:
							'''
							print 'True'
							output.write('True')
							output.write('\n')
							'''
							return
							#raise StopIteration
							
							
				yield thetaR
	yield None
				

def Fol_bc_and(KB,goals,theta):
	print 'Inside the Fol_bc_and'
	if theta is None: 
		return
	elif len(goals) == 0: #	if the rule is an atomic sentence, lhs would be None	
		yield theta
	else:
		first, rest = goals[0], goals[1:]

		senNew = subst(theta, first)
		for theta1 in Fol_bc_or(KB, senNew, theta):
			for theta2 in Fol_bc_and(KB, rest, theta1):
				yield theta2

def subst(theta, sentence):
	print 'Inside the subst'
	senNew = copy.deepcopy(sentence)
	if theta is None:
		return senNew
	for arg in theta:
		for i in range(0,len(senNew['arg'])):
			if senNew['arg'][i] == arg:
				senNew['arg'][i] = theta[arg]
	return senNew	

def kb_ask(kb, query_list):
	for query in query_list:
   		if not Fol_bc_ask(kb, query):
   			return False
	return True

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
	query = Str_to_clause(line,count)
	count += 1
for line in file:
	line = line.strip('\n')
	kb.clauses.append(Str_to_clause(line,count))
	count += 1
	if count == num+1:
		break
standCount = 'a'
output = open('./output.txt','w')
print 'start ================================================'
output.write(str(kb_ask(kb,query['conclusion'])))

output.close()
print 'end============================================='