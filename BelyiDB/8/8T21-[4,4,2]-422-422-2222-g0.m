s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T21-[4,4,2]-422-422-2222-g0";
s`BelyiDBFilename := "8T21-[4,4,2]-422-422-2222-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 4, 4, 2 ];
s`BelyiDBType := "Euclidean";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 5, 2, 7, 4, 1, 6, 3, 8 ],
\[ 4, 3, 2, 5, 8, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ]:
 Order := 32 > |
[ 4, 3, 2, 5, 8, 7, 6, 1 ],
[ 2, 5, 8, 7, 6, 1, 4, 3 ],
[ 3, 8, 1, 6, 7, 4, 5, 2 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 4, 3, 2, 5, 8, 7, 6, 1 ],
\[ 2, 5, 8, 7, 6, 1, 4, 3 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ]:
 Order := 32 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 4, 3, 2, 5, 8, 7, 6, 1 ],
\[ 2, 5, 8, 7, 6, 1, 4, 3 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ]:
 Order := 32 >) |
[ PermutationGroup<8 |  
\[ 4, 3, 2, 5, 8, 7, 6, 1 ],
\[ 2, 5, 8, 7, 6, 1, 4, 3 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ]:
 Order := 32 > |
[ 4, 3, 2, 5, 8, 7, 6, 1 ],
[ 2, 5, 8, 7, 6, 1, 4, 3 ],
[ 3, 8, 1, 6, 7, 4, 5, 2 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 5, 2, 7, 4, 1, 6, 3, 8 ],
\[ 4, 3, 2, 5, 8, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ]:
 Order := 32 >) |
[ PermutationGroup<8 |  
\[ 5, 2, 7, 4, 1, 6, 3, 8 ],
\[ 4, 3, 2, 5, 8, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ]:
 Order := 32 > |
[ 4, 3, 2, 5, 8, 7, 6, 1 ],
[ 2, 5, 8, 7, 6, 1, 4, 3 ],
[ 3, 8, 1, 6, 7, 4, 5, 2 ]
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
