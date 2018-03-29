s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "7T5-[7,7,7]-7-7-7-g3";
s`BelyiDBFilename := "7T5-[7,7,7]-7-7-7-g3.m";
s`BelyiDBDegree := 7;
s`BelyiDBOrders := \[ 7, 7, 7 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 3;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<7 |  
\[ 2, 3, 4, 5, 6, 7, 1 ],
\[ 2, 1, 6, 4, 5, 3, 7 ]:
 Order := 168 > |
[ 4, 5, 6, 7, 1, 2, 3 ],
[ 4, 3, 1, 6, 7, 5, 2 ],
[ 6, 4, 5, 3, 7, 2, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<7 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<7 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<7 |  
\[ 4, 5, 6, 7, 1, 2, 3 ],
\[ 4, 3, 1, 6, 7, 5, 2 ],
\[ 6, 4, 5, 3, 7, 2, 1 ]:
 Order := 168 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<7 |  
\[ 4, 5, 6, 7, 1, 2, 3 ],
\[ 4, 3, 1, 6, 7, 5, 2 ],
\[ 6, 4, 5, 3, 7, 2, 1 ]:
 Order := 168 >) |
[ PermutationGroup<7 |  
\[ 4, 5, 6, 7, 1, 2, 3 ],
\[ 4, 3, 1, 6, 7, 5, 2 ],
\[ 6, 4, 5, 3, 7, 2, 1 ]:
 Order := 168 > |
[ 4, 5, 6, 7, 1, 2, 3 ],
[ 4, 3, 1, 6, 7, 5, 2 ],
[ 6, 4, 5, 3, 7, 2, 1 ]
],
[ PermutationGroup<7 |  
\[ 4, 5, 6, 7, 1, 2, 3 ],
\[ 4, 3, 1, 6, 7, 5, 2 ],
\[ 6, 4, 5, 3, 7, 2, 1 ]:
 Order := 168 > |
[ 3, 4, 5, 6, 7, 1, 2 ],
[ 7, 4, 2, 5, 1, 3, 6 ],
[ 7, 1, 5, 3, 6, 2, 4 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<7 |  
\[ 2, 3, 4, 5, 6, 7, 1 ],
\[ 2, 1, 6, 4, 5, 3, 7 ]:
 Order := 168 >) |
[ PermutationGroup<7 |  
\[ 2, 3, 4, 5, 6, 7, 1 ],
\[ 2, 1, 6, 4, 5, 3, 7 ]:
 Order := 168 > |
[ 4, 5, 6, 7, 1, 2, 3 ],
[ 4, 3, 1, 6, 7, 5, 2 ],
[ 6, 4, 5, 3, 7, 2, 1 ]
],
[ PermutationGroup<7 |  
\[ 2, 3, 4, 5, 6, 7, 1 ],
\[ 2, 1, 6, 4, 5, 3, 7 ]:
 Order := 168 > |
[ 2, 3, 4, 5, 6, 7, 1 ],
[ 2, 6, 5, 7, 1, 4, 3 ],
[ 4, 5, 1, 7, 6, 3, 2 ]
]
];

/*
Base Field Data
*/


/*
Belyi Maps
*/


/*
Powser Bases
*/


/*
Return for eval
*/

return s;
